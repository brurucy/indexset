use std::sync::atomic::AtomicUsize;
use std::{borrow::Borrow, sync::Arc};

use parking_lot::{Mutex, RwLock};

use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

use scc::ebr::Shared;

use std::cell::UnsafeCell;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::mem::{needs_drop, MaybeUninit};
use std::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

/// Key equivalence trait.
///
/// [`Hash`](std::hash::Hash) will have to be implemented to make sure that the same hash value
/// is generated for equivalent keys.
pub trait Equivalent<K: ?Sized> {
    /// Compares `self` to `key` and returns `true` if they are equal.
    fn equivalent(&self, key: &K) -> bool;
}

impl<Q: ?Sized, K: ?Sized> Equivalent<K> for Q
where
    Q: Eq,
    K: Borrow<Q>,
{
    #[inline]
    fn equivalent(&self, key: &K) -> bool {
        PartialEq::eq(self, key.borrow())
    }
}

/// Key ordering trait.
pub trait Comparable<K: ?Sized>: Equivalent<K> {
    /// Compares `self` to `key` and returns their ordering.
    fn compare(&self, key: &K) -> Ordering;
}

impl<Q: ?Sized, K: ?Sized> Comparable<K> for Q
where
    Q: Ord,
    K: Borrow<Q>,
{
    #[inline]
    fn compare(&self, key: &K) -> Ordering {
        Ord::cmp(self, key.borrow())
    }
}

/// [`Leaf`] is an ordered array of key-value pairs.
///
/// A constructed key-value pair entry is never dropped until the entire [`Leaf`] instance is
/// dropped.
pub struct Leaf<K, V> {
    /// The metadata containing information about the [`Leaf`] and individual entries.
    ///
    /// The state of each entry is as follows.
    /// * `0`: `uninit`.
    /// * `1-ARRAY_SIZE`: `rank`.
    /// * `ARRAY_SIZE + 1`: `removed`.
    ///
    /// The entry state transitions as follows.
    /// * `uninit -> removed -> rank -> removed`.
    metadata: AtomicUsize,

    /// The array of key-value pairs.
    entry_array: UnsafeCell<EntryArray<K, V>>,
}

/// The number of entries and number of state bits per entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Dimension {
    pub num_entries: usize,
    pub num_bits_per_entry: usize,
}

/// The result of insertion.
pub enum InsertResult<K, V> {
    /// Insertion succeeded.
    Success,

    /// Duplicate key found.
    Duplicate(K, V),

    /// No vacant slot for the key.
    Full(K, V),

    /// The [`Leaf`] is frozen.
    ///
    /// It is not a terminal state that a frozen [`Leaf`] can be unfrozen.
    Frozen(K, V),

    /// Insertion failed as the [`Leaf`] has retired.
    ///
    /// It is a terminal state.
    Retired(K, V),

    /// The operation can be retried.
    Retry(K, V),
}

/// The result of removal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RemoveResult {
    /// Remove succeeded.
    Success,

    /// Remove succeeded and cleanup required.
    Cleanup,

    /// Remove succeeded and the [`Leaf`] has retired without usable entries left.
    Retired,

    /// Remove failed.
    Fail,

    /// The [`Leaf`] is frozen.
    Frozen,
}

impl<K, V> Leaf<K, V> {
    /// Creates a new [`Leaf`].
    #[inline]
    pub(super) const fn new() -> Leaf<K, V> {
        #[allow(clippy::uninit_assumed_init)]
        Leaf {
            metadata: AtomicUsize::new(0),
            entry_array: UnsafeCell::new(unsafe { MaybeUninit::uninit().assume_init() }),
        }
    }

    /// Thaws the [`Leaf`].
    #[inline]
    pub(super) fn thaw(&self) -> bool {
        self.metadata
            .fetch_update(Release, Relaxed, |p| {
                if Dimension::frozen(p) {
                    Some(Dimension::thaw(p))
                } else {
                    None
                }
            })
            .is_ok()
    }

    /// Returns `true` if the [`Leaf`] has retired.
    #[inline]
    pub(super) fn is_retired(&self) -> bool {
        Dimension::retired(self.metadata.load(Acquire))
    }

    /// Returns `true` if the [`Leaf`] has no reachable entry.
    #[inline]
    pub(super) fn is_empty(&self) -> bool {
        let mut mutable_metadata = self.metadata.load(Acquire);
        for _ in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank != Dimension::uninit_rank() && rank != DIMENSION.removed_rank() {
                return false;
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        true
    }

    /// Returns a reference to the max key.
    #[inline]
    pub(super) fn max_key(&self) -> Option<&K> {
        self.max_entry().map(|(k, _)| k)
    }

    /// Returns a reference to the max entry.
    #[inline]
    pub(super) fn max_entry(&self) -> Option<(&K, &V)> {
        let mut mutable_metadata = self.metadata.load(Acquire);
        let mut max_rank = 0;
        let mut max_index = DIMENSION.num_entries;
        for i in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank > max_rank && rank != DIMENSION.removed_rank() {
                max_rank = rank;
                max_index = i;
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        if max_index != DIMENSION.num_entries {
            return Some((self.key_at(max_index), self.value_at(max_index)));
        }
        None
    }

    /// Inserts a key value pair at the specified position without checking the metadata.
    ///
    /// `rank` is calculated as `index + 1`.
    #[inline]
    pub(super) fn insert_unchecked(&self, key: K, val: V, index: usize) {
        debug_assert!(index < DIMENSION.num_entries);
        let metadata = self.metadata.load(Relaxed);
        let new_metadata = DIMENSION.augment(metadata, index, index + 1);
        self.write(index, key, val);
        self.metadata.store(new_metadata, Release);
    }

    /// Compares the given metadata value with the current one.
    #[inline]
    pub(super) fn validate(&self, metadata: usize) -> bool {
        // `Relaxed` is sufficient as long as the caller has load-acquired its contents.
        self.metadata.load(Relaxed) == metadata
    }

    /// Freezes the [`Leaf`] temporarily.
    ///
    /// A frozen [`Leaf`] cannot store more entries, and on-going insertion is canceled.
    #[inline]
    pub(super) fn freeze(&self) -> bool {
        self.metadata
            .fetch_update(AcqRel, Acquire, |p| {
                if Dimension::frozen(p) {
                    None
                } else {
                    Some(Dimension::freeze(p))
                }
            })
            .is_ok()
    }

    /// Returns the recommended number of entries that the left-side node shall store when a
    /// [`Leaf`] is split.
    ///
    /// Returns a number in `[1, len(leaf))` that represents the recommended number of entries in
    /// the left-side node. The number is calculated as, for each adjacent slots,
    /// - Initial `score = len(leaf)`.
    /// - Rank increased: `score -= 1`.
    /// - Rank decreased: `score += 1`.
    /// - Clamp `score` in `[len(leaf) / 2 + 1, len(leaf) / 2 + len(leaf) - 1)`.
    /// - Take `score - len(leaf) / 2`.
    ///
    /// For instance, when the length of a [`Leaf`] is 7,
    /// - Returns 6 for `rank = [1, 2, 3, 4, 5, 6, 7]`.
    /// - Returns 1 for `rank = [7, 6, 5, 4, 3, 2, 1]`.
    #[inline]
    pub(super) fn optimal_boundary(mut mutable_metadata: usize) -> usize {
        let mut boundary: usize = DIMENSION.num_entries;
        let mut prev_rank = 0;
        for _ in 0..DIMENSION.num_entries {
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank != 0 && rank != DIMENSION.removed_rank() {
                if prev_rank >= rank {
                    boundary -= 1;
                } else if prev_rank != 0 {
                    boundary += 1;
                }
                prev_rank = rank;
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        boundary.clamp(
            DIMENSION.num_entries / 2 + 1,
            DIMENSION.num_entries + DIMENSION.num_entries / 2 - 1,
        ) - DIMENSION.num_entries / 2
    }

    fn key_at(&self, index: usize) -> &K {
        unsafe { &*(*self.entry_array.get()).0[index].as_ptr() }
    }

    fn value_at(&self, index: usize) -> &V {
        unsafe { &*(*self.entry_array.get()).1[index].as_ptr() }
    }

    fn rollback(&self, index: usize) -> InsertResult<K, V> {
        let (key, val) = self.take(index);
        let result = self
            .metadata
            .fetch_and(!DIMENSION.rank_mask(index), Release)
            & (!DIMENSION.rank_mask(index));
        if Dimension::retired(result) {
            InsertResult::Retired(key, val)
        } else if Dimension::frozen(result) {
            InsertResult::Frozen(key, val)
        } else {
            InsertResult::Duplicate(key, val)
        }
    }

    fn take(&self, index: usize) -> (K, V) {
        unsafe {
            (
                (*self.entry_array.get()).0[index].as_ptr().read(),
                (*self.entry_array.get()).1[index].as_ptr().read(),
            )
        }
    }

    fn write(&self, index: usize, key: K, val: V) {
        unsafe {
            (*self.entry_array.get()).0[index].as_mut_ptr().write(key);
            (*self.entry_array.get()).1[index].as_mut_ptr().write(val);
        }
    }

    /// Returns the index of the corresponding entry of the next higher ranked entry.
    fn next(index: usize, mut mutable_metadata: usize) -> usize {
        debug_assert_ne!(index, usize::MAX);
        let current_entry_rank = if index == DIMENSION.num_entries {
            0
        } else {
            DIMENSION.rank(mutable_metadata, index)
        };
        let mut next_index = DIMENSION.num_entries;
        if current_entry_rank < DIMENSION.num_entries {
            let mut next_rank = DIMENSION.removed_rank();
            for i in 0..DIMENSION.num_entries {
                if mutable_metadata == 0 {
                    break;
                }
                if i != index {
                    let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
                    if rank != Dimension::uninit_rank() && rank < next_rank {
                        if rank == current_entry_rank + 1 {
                            return i;
                        } else if rank > current_entry_rank {
                            next_rank = rank;
                            next_index = i;
                        }
                    }
                }
                mutable_metadata >>= DIMENSION.num_bits_per_entry;
            }
        }
        next_index
    }
}

impl<K, V> Leaf<K, V>
where
    K: 'static + Clone + Ord,
    V: 'static + Clone,
{
    /// Inserts a key value pair.
    #[inline]
    pub(super) fn insert(&self, key: K, val: V) -> InsertResult<K, V> {
        let mut metadata = self.metadata.load(Acquire);
        'after_read_metadata: loop {
            if Dimension::retired(metadata) {
                return InsertResult::Retired(key, val);
            } else if Dimension::frozen(metadata) {
                return InsertResult::Frozen(key, val);
            }

            let mut mutable_metadata = metadata;
            for i in 0..DIMENSION.num_entries {
                let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
                if rank == Dimension::uninit_rank() {
                    let interim_metadata = DIMENSION.augment(metadata, i, DIMENSION.removed_rank());

                    // Reserve the slot.
                    //
                    // It doesn't have to be a release-store.
                    if let Err(actual) =
                        self.metadata
                            .compare_exchange(metadata, interim_metadata, Acquire, Acquire)
                    {
                        metadata = actual;
                        continue 'after_read_metadata;
                    }

                    self.write(i, key, val);
                    return self.post_insert(i, interim_metadata);
                }
                mutable_metadata >>= DIMENSION.num_bits_per_entry;
            }

            if self.search_slot(&key, metadata).is_some() {
                return InsertResult::Duplicate(key, val);
            }
            return InsertResult::Full(key, val);
        }
    }

    /// Removes the key if the condition is met.
    #[inline]
    pub(super) fn remove_if<Q, F: FnMut(&V) -> bool>(
        &self,
        key: &Q,
        condition: &mut F,
    ) -> RemoveResult
    where
        Q: Comparable<K> + ?Sized,
    {
        let mut metadata = self.metadata.load(Acquire);
        if Dimension::frozen(metadata) {
            return RemoveResult::Frozen;
        }
        let mut min_max_rank = DIMENSION.removed_rank();
        let mut max_min_rank = 0;
        let mut mutable_metadata = metadata;
        for i in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank < min_max_rank && rank > max_min_rank {
                match self.compare(i, key) {
                    Ordering::Less => {
                        if max_min_rank < rank {
                            max_min_rank = rank;
                        }
                    }
                    Ordering::Greater => {
                        if min_max_rank > rank {
                            min_max_rank = rank;
                        }
                    }
                    Ordering::Equal => {
                        // Found the key.
                        loop {
                            if !condition(self.value_at(i)) {
                                // The given condition is not met.
                                return RemoveResult::Fail;
                            }
                            let mut empty = true;
                            mutable_metadata = metadata;
                            for j in 0..DIMENSION.num_entries {
                                if mutable_metadata == 0 {
                                    break;
                                }
                                if i != j {
                                    let rank = mutable_metadata
                                        % (1_usize << DIMENSION.num_bits_per_entry);
                                    if rank != Dimension::uninit_rank()
                                        && rank != DIMENSION.removed_rank()
                                    {
                                        empty = false;
                                        break;
                                    }
                                }
                                mutable_metadata >>= DIMENSION.num_bits_per_entry;
                            }

                            let mut new_metadata = metadata | DIMENSION.rank_mask(i);
                            if empty {
                                new_metadata = Dimension::retire(new_metadata);
                            }
                            match self.metadata.compare_exchange(
                                metadata,
                                new_metadata,
                                AcqRel,
                                Acquire,
                            ) {
                                Ok(_) => {
                                    if empty {
                                        return RemoveResult::Retired;
                                    }
                                    return RemoveResult::Success;
                                }
                                Err(actual) => {
                                    if DIMENSION.rank(actual, i) == DIMENSION.removed_rank() {
                                        return RemoveResult::Fail;
                                    }
                                    if Dimension::frozen(actual) {
                                        return RemoveResult::Frozen;
                                    }
                                    metadata = actual;
                                }
                            }
                        }
                    }
                };
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }

        RemoveResult::Fail
    }

    /// Returns an entry containing the specified key.
    #[inline]
    pub(super) fn search_entry<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Comparable<K> + ?Sized,
    {
        let metadata = self.metadata.load(Acquire);
        self.search_slot(key, metadata)
            .map(|i| (self.key_at(i), self.value_at(i)))
    }

    /// Returns the value associated with the specified key.
    #[inline]
    pub(super) fn search_value<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Comparable<K> + ?Sized,
    {
        let metadata = self.metadata.load(Acquire);
        self.search_slot(key, metadata).map(|i| self.value_at(i))
    }

    /// Returns the index of the key-value pair that is smaller than the given key.
    #[inline]
    pub(super) fn max_less<Q>(&self, mut mutable_metadata: usize, key: &Q) -> usize
    where
        Q: Comparable<K> + ?Sized,
    {
        let mut min_max_rank = DIMENSION.removed_rank();
        let mut max_min_rank = 0;
        let mut max_min_index = DIMENSION.num_entries;
        for i in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank < min_max_rank && rank > max_min_rank {
                match self.compare(i, key) {
                    Ordering::Less => {
                        if max_min_rank < rank {
                            max_min_rank = rank;
                            max_min_index = i;
                        }
                    }
                    Ordering::Greater => {
                        if min_max_rank > rank {
                            min_max_rank = rank;
                        }
                    }
                    Ordering::Equal => {
                        min_max_rank = rank;
                    }
                }
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        max_min_index
    }

    /// Returns the minimum entry among those that are not `Ordering::Less` than the given key.
    ///
    /// It additionally returns the current version of its metadata in order for the caller to
    /// validate the sanity of the result.
    #[inline]
    pub(super) fn min_greater_equal<Q>(&self, key: &Q) -> (Option<(&K, &V)>, usize)
    where
        Q: Comparable<K> + ?Sized,
    {
        let metadata = self.metadata.load(Acquire);
        let mut min_max_rank = DIMENSION.removed_rank();
        let mut max_min_rank = 0;
        let mut min_max_index = DIMENSION.num_entries;
        let mut mutable_metadata = metadata;
        for i in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank < min_max_rank && rank > max_min_rank {
                let k = self.key_at(i);
                match key.compare(k) {
                    Ordering::Greater => {
                        if max_min_rank < rank {
                            max_min_rank = rank;
                        }
                    }
                    Ordering::Less => {
                        if min_max_rank > rank {
                            min_max_rank = rank;
                            min_max_index = i;
                        }
                    }
                    Ordering::Equal => {
                        return (Some((k, self.value_at(i))), metadata);
                    }
                }
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        if min_max_index != DIMENSION.num_entries {
            return (
                Some((self.key_at(min_max_index), self.value_at(min_max_index))),
                metadata,
            );
        }
        (None, metadata)
    }

    /// Freezes the [`Leaf`] and distribute entries to two new leaves.
    #[inline]
    pub(super) fn freeze_and_distribute(
        &self,
        low_key_leaf: &mut Option<Shared<Leaf<K, V>>>,
        high_key_leaf: &mut Option<Shared<Leaf<K, V>>>,
    ) {
        let metadata = unsafe {
            self.metadata
                .fetch_update(AcqRel, Acquire, |p| {
                    if Dimension::frozen(p) {
                        None
                    } else {
                        Some(Dimension::freeze(p))
                    }
                })
                .unwrap_unchecked()
        };

        let boundary = Self::optimal_boundary(metadata);
        let scanner = Scanner {
            leaf: self,
            metadata,
            entry_index: DIMENSION.num_entries,
        };
        for (i, (k, v)) in scanner.enumerate() {
            if i < boundary {
                low_key_leaf
                    .get_or_insert_with(|| Shared::new(Leaf::new()))
                    .insert_unchecked(k.clone(), v.clone(), i);
            } else {
                high_key_leaf
                    .get_or_insert_with(|| Shared::new(Leaf::new()))
                    .insert_unchecked(k.clone(), v.clone(), i - boundary);
            };
        }
    }

    /// Post-processing after reserving a free slot.
    fn post_insert(&self, free_slot_index: usize, mut prev_metadata: usize) -> InsertResult<K, V> {
        let key = self.key_at(free_slot_index);
        loop {
            let mut min_max_rank = DIMENSION.removed_rank();
            let mut max_min_rank = 0;
            let mut new_metadata = prev_metadata;
            let mut mutable_metadata = prev_metadata;
            for i in 0..DIMENSION.num_entries {
                if mutable_metadata == 0 {
                    break;
                }
                let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
                if rank < min_max_rank && rank > max_min_rank {
                    match self.compare(i, key) {
                        Ordering::Less => {
                            if max_min_rank < rank {
                                max_min_rank = rank;
                            }
                        }
                        Ordering::Greater => {
                            if min_max_rank > rank {
                                min_max_rank = rank;
                            }
                            new_metadata = DIMENSION.augment(new_metadata, i, rank + 1);
                        }
                        Ordering::Equal => {
                            // Duplicate key.
                            return self.rollback(free_slot_index);
                        }
                    }
                } else if rank != DIMENSION.removed_rank() && rank > min_max_rank {
                    new_metadata = DIMENSION.augment(new_metadata, i, rank + 1);
                }
                mutable_metadata >>= DIMENSION.num_bits_per_entry;
            }

            // Make the newly inserted value reachable.
            let final_metadata = DIMENSION.augment(new_metadata, free_slot_index, max_min_rank + 1);
            if let Err(actual) =
                self.metadata
                    .compare_exchange(prev_metadata, final_metadata, AcqRel, Acquire)
            {
                if Dimension::frozen(actual) || Dimension::retired(actual) {
                    return self.rollback(free_slot_index);
                }
                prev_metadata = actual;
                continue;
            }

            return InsertResult::Success;
        }
    }

    /// Searches for a slot in which the key is stored.
    fn search_slot<Q>(&self, key: &Q, mut mutable_metadata: usize) -> Option<usize>
    where
        Q: Comparable<K> + ?Sized,
    {
        let mut min_max_rank = DIMENSION.removed_rank();
        let mut max_min_rank = 0;
        for i in 0..DIMENSION.num_entries {
            if mutable_metadata == 0 {
                break;
            }
            let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
            if rank < min_max_rank && rank > max_min_rank {
                match self.compare(i, key) {
                    Ordering::Less => {
                        if max_min_rank < rank {
                            max_min_rank = rank;
                        }
                    }
                    Ordering::Greater => {
                        if min_max_rank > rank {
                            min_max_rank = rank;
                        }
                    }
                    Ordering::Equal => {
                        return Some(i);
                    }
                }
            }
            mutable_metadata >>= DIMENSION.num_bits_per_entry;
        }
        None
    }

    fn compare<Q>(&self, index: usize, key: &Q) -> Ordering
    where
        Q: Comparable<K> + ?Sized,
    {
        key.compare(self.key_at(index)).reverse()
    }
}

impl<K, V> Drop for Leaf<K, V> {
    #[inline]
    fn drop(&mut self) {
        if needs_drop::<(K, V)>() {
            let mut mutable_metadata = self.metadata.load(Acquire);
            for i in 0..DIMENSION.num_entries {
                if mutable_metadata == 0 {
                    break;
                }
                if mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry)
                    != Dimension::uninit_rank()
                {
                    self.take(i);
                }
                mutable_metadata >>= DIMENSION.num_bits_per_entry;
            }
        }
    }
}

unsafe impl<K: Send, V: Send> Send for Leaf<K, V> {}

unsafe impl<K: Sync, V: Sync> Sync for Leaf<K, V> {}

impl Dimension {
    /// Checks if the [`Leaf`] is frozen.
    const fn frozen(metadata: usize) -> bool {
        metadata & (1_usize << (usize::BITS - 2)) != 0
    }

    /// Makes the metadata represent a frozen state.
    const fn freeze(metadata: usize) -> usize {
        metadata | (1_usize << (usize::BITS - 2))
    }

    /// Updates the metadata to represent a non-frozen state.
    const fn thaw(metadata: usize) -> usize {
        metadata & (!(1_usize << (usize::BITS - 2)))
    }

    /// Checks if the [`Leaf`] is retired.
    const fn retired(metadata: usize) -> bool {
        metadata & (1_usize << (usize::BITS - 1)) != 0
    }

    /// Makes the metadata represent a retired state.
    const fn retire(metadata: usize) -> usize {
        metadata | (1_usize << (usize::BITS - 1))
    }

    /// Returns a bit mask for an entry.
    const fn rank_mask(&self, index: usize) -> usize {
        ((1_usize << self.num_bits_per_entry) - 1) << (index * self.num_bits_per_entry)
    }

    /// Returns the rank of an entry.
    const fn rank(&self, metadata: usize, index: usize) -> usize {
        (metadata >> (index * self.num_bits_per_entry)) % (1_usize << self.num_bits_per_entry)
    }

    /// Returns the uninitialized rank value which is smaller than all the valid rank values.
    const fn uninit_rank() -> usize {
        0
    }

    /// Returns the removed rank value which is greater than all the valid rank values.
    const fn removed_rank(&self) -> usize {
        (1_usize << self.num_bits_per_entry) - 1
    }

    /// Augments the rank to the given metadata.
    const fn augment(&self, metadata: usize, index: usize, rank: usize) -> usize {
        (metadata & (!self.rank_mask(index))) | (rank << (index * self.num_bits_per_entry))
    }
}

/// The maximum number of entries and the number of metadata bits per entry in a [`Leaf`].
///
/// * `M`: The maximum number of entries.
/// * `B`: The minimum number of bits to express the state of an entry.
/// * `2`: The number of special states of an entry: uninitialized, removed.
/// * `2`: The number of special states of a [`Leaf`]: frozen, retired.
/// * `U`: `usize::BITS`.
/// * `Eq1 = M + 2 <= 2^B`: `B` bits represent at least `M + 2` states.
/// * `Eq2 = B * M + 2 <= U`: `M entries + 2` special state.
/// * `Eq3 = Ceil(Log2(M + 2)) * M + 2 <= U`: derived from `Eq1` and `Eq2`.
///
/// Therefore, when `U = 64 => M = 14 / B = 4`, and `U = 32 => M = 7 / B = 4`.
pub const DIMENSION: Dimension = match usize::BITS / 8 {
    1 => Dimension {
        num_entries: 2,
        num_bits_per_entry: 2,
    },
    2 => Dimension {
        num_entries: 4,
        num_bits_per_entry: 3,
    },
    4 => Dimension {
        num_entries: 7,
        num_bits_per_entry: 4,
    },
    8 => Dimension {
        num_entries: 14,
        num_bits_per_entry: 4,
    },
    _ => Dimension {
        num_entries: 25,
        num_bits_per_entry: 5,
    },
};

/// Each constructed entry in an `EntryArray` is never dropped until the [`Leaf`] is dropped.
pub type EntryArray<K, V> = (
    [MaybeUninit<K>; DIMENSION.num_entries],
    [MaybeUninit<V>; DIMENSION.num_entries],
);

/// Leaf scanner.
pub struct Scanner<'l, K, V> {
    leaf: &'l Leaf<K, V>,
    metadata: usize,
    entry_index: usize,
}

impl<'l, K, V> Scanner<'l, K, V> {
    /// Creates a new [`Scanner`].
    #[inline]
    pub(super) fn new(leaf: &'l Leaf<K, V>) -> Scanner<'l, K, V> {
        Scanner {
            leaf,
            metadata: leaf.metadata.load(Acquire),
            entry_index: DIMENSION.num_entries,
        }
    }

    /// Returns the metadata that the [`Scanner`] is currently using.
    #[inline]
    pub(super) const fn metadata(&self) -> usize {
        self.metadata
    }

    /// Returns a reference to the entry that the scanner is currently pointing to
    #[inline]
    pub(super) fn get(&self) -> Option<(&'l K, &'l V)> {
        if self.entry_index >= DIMENSION.num_entries {
            return None;
        }
        Some((
            self.leaf.key_at(self.entry_index),
            self.leaf.value_at(self.entry_index),
        ))
    }

    /// Returns a reference to the max key.
    #[inline]
    pub(super) fn max_key(&self) -> Option<&'l K> {
        self.leaf.max_key()
    }

    fn proceed(&mut self) {
        if self.entry_index == usize::MAX {
            return;
        }
        let index = Leaf::<K, V>::next(self.entry_index, self.metadata);
        if index == DIMENSION.num_entries {
            // Fuse the iterator.
            self.entry_index = usize::MAX;
        } else {
            self.entry_index = index;
        }
    }
}

impl<'l, K, V> Scanner<'l, K, V>
where
    K: 'static + Clone + Ord,
    V: 'static + Clone,
{
    /// Returns a [`Scanner`] pointing to the max-less entry if there is one.
    #[inline]
    pub(super) fn max_less<Q>(leaf: &'l Leaf<K, V>, key: &Q) -> Option<Scanner<'l, K, V>>
    where
        Q: Comparable<K> + ?Sized,
    {
        let metadata = leaf.metadata.load(Acquire);
        let index = leaf.max_less(metadata, key);
        if index == DIMENSION.num_entries {
            None
        } else {
            Some(Scanner {
                leaf,
                metadata,
                entry_index: index,
            })
        }
    }
}

impl<'l, K, V> Debug for Scanner<'l, K, V> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Scanner")
            .field("metadata", &self.metadata)
            .field("entry_index", &self.entry_index)
            .finish()
    }
}

impl<'l, K, V> Iterator for Scanner<'l, K, V> {
    type Item = (&'l K, &'l V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.proceed();
        self.get()
    }
}

#[derive(Debug)]
pub struct BTreeSet<T>
where
    T: Ord,
{
    node_capacity: usize,
    inner: RwLock<Vec<Arc<Mutex<Vec<T>>>>>,
}
impl<T: Ord> Default for BTreeSet<T> {
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE;

        Self {
            node_capacity,
            inner: RwLock::new(vec![Arc::new(Mutex::new(Vec::with_capacity(
                node_capacity,
            )))]),
        }
    }
}

impl<T: Ord + Clone> BTreeSet<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&self, value: T) -> bool {
        let global_read_lock = self.inner.read();
        let mut node_idx = global_read_lock.partition_point(|node| {
            if let Some(&max) = node.lock().last().as_ref() {
                return max.borrow() < &value;
            };
            false
        });
        if global_read_lock.get(node_idx).is_none() {
            node_idx -= 1
        }
        if let Some(node) = global_read_lock.get(node_idx).cloned() {
            let mut node_write_lock = node.lock();
            if node_write_lock.len() == self.node_capacity {
                if NodeLike::insert(&mut *node_write_lock, value) {
                    drop(global_read_lock);
                    drop(node_write_lock);
                    let mut global_write_lock = self.inner.write();
                    let mut node_write_lock = node.lock();
                    let new_node = node_write_lock.halve();
                    global_write_lock.insert(node_idx + 1, Arc::new(Mutex::new(new_node)));

                    return true;
                }
            } else {
                return NodeLike::insert(&mut *node_write_lock, value);
            }
        }

        false
    }
    fn locate_node<Q>(&self, value: &Q) -> Option<Arc<Mutex<Vec<T>>>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let global_read_lock = self.inner.read();
        let mut node_idx = global_read_lock.partition_point(|node| {
            if let Some(&max) = node.lock().last().as_ref() {
                return max.borrow() < value;
            };
            false
        });
        // When value is greater than all elements inside inner[node_idx], then len
        // of inner[node_idx], which is not a valid place for insertion, is returned. It will
        // never return less than 0, so it is only necessary to check whether it is out of bounds
        // from the right
        if global_read_lock.get(node_idx).is_none() {
            node_idx -= 1
        }
        global_read_lock.get(node_idx).cloned()
    }
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(node) = self.locate_node(value) {
            return node.lock().contains(value);
        }
        false
    }
    pub fn len(&self) -> usize {
        let global_read_lock = self.inner.read();
        global_read_lock.iter().map(|node| node.lock().len()).sum()
    }
}

#[cfg(test)]
mod tests {
    use crate::concurrent2::set::BTreeSet;
    use rand::Rng;
    use std::collections::HashSet;
    use std::sync::{Arc, Mutex};
    use std::thread;

    #[test]
    fn test_concurrent_insert() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let num_threads = 8;
        let operations_per_thread = 1000;
        let mut handles = vec![];

        let test_data: Vec<Vec<(i32, i32)>> = (0..num_threads)
            .map(|_| {
                let mut rng = rand::thread_rng();
                (0..operations_per_thread)
                    .map(|_| {
                        let value = rng.gen_range(0..10000);
                        let operation = rng.gen_range(0..2);
                        (operation, value)
                    })
                    .collect()
            })
            .collect();

        let expected_values = Arc::new(Mutex::new(HashSet::new()));

        for thread_idx in 0..num_threads {
            let set_clone = Arc::clone(&set);
            let expected_values = Arc::clone(&expected_values);
            let thread_data = test_data[thread_idx].clone();

            let handle = thread::spawn(move || {
                for (operation, value) in thread_data {
                    if operation == 0 {
                        set_clone.insert(value);
                        //if set_clone.insert(value) {
                        expected_values.lock().unwrap().insert(value);
                        //}
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let expected_values = expected_values.lock().unwrap();
        println!("AAA {}", set.len());
        assert_eq!(set.len(), expected_values.len());

        for value in expected_values.iter() {
            assert!(set.contains(value), "Missing value: {}", value);
        }
    }

    #[test]
    fn test_insert_st() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let range = 0..100_000;
        for i in range {
            set.insert(i);
        }

        assert_eq!(set.len(), 100_000);
        for i in 0..100_000 {
            set.contains(&i);
        }
    }
}
