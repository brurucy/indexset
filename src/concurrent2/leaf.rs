use core::fmt;
use std::{
    cell::UnsafeCell,
    cmp::Ordering,
    fmt::Debug,
    mem::{needs_drop, MaybeUninit},
    sync::atomic::{
        AtomicBool, AtomicU8,
        Ordering::{AcqRel, Acquire, Relaxed, Release},
    },
};

use scc::ebr::Shared;

use std::sync::atomic::AtomicUsize;

use super::{
    comparable::Comparable,
    metadata::{Dimension, DIMENSION},
};
/// The number of entries and number of state bits per entry.
/// [`Leaf`] is an ordered array of key-value pairs.
///
/// A constructed key-value pair entry is never dropped until the entire [`Leaf`] instance is
/// dropped.
type METADATA = [AtomicU8; 8];

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
    pub(crate) metadata: AtomicUsize,

    /// The array of key-value pairs.
    pub(crate) entry_array: UnsafeCell<EntryArray<K, V>>,
}

type ENTRY_METADATA = AtomicU8;
type LEAF_METADATA = [ENTRY_METADATA; 9];

const UNINIT_RANK: u8 = 0;
const REMOVED_RANK: u8 = u8::MAX; // 255
                                  // For the status byte (last byte in array)
const FROZEN_BIT: u8 = 0b0100_0000; // Second to last bit
const RETIRED_BIT: u8 = 0b1000_0000; // Last bit

pub struct SimpleLeaf<K, V> {
    pub(crate) metadata: LEAF_METADATA, // [AtomicU8; 9]
    pub(crate) entry_array: UnsafeCell<EntryArray<K, V>>,
}
unsafe impl<K: Send, V: Send> Send for SimpleLeaf<K, V> {}

unsafe impl<K: Sync, V: Sync> Sync for SimpleLeaf<K, V> {}

impl<K, V> SimpleLeaf<K, V> {
    fn new() -> Self {
        Self {
            metadata: [
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
                AtomicU8::new(0),
            ],
            entry_array: UnsafeCell::new(unsafe { MaybeUninit::uninit().assume_init() }),
        }
    }
}

impl<K, V> SimpleLeaf<K, V> {
    #[inline]
    fn status_byte(&self) -> &AtomicU8 {
        &self.metadata[8] // Last byte for status
    }

    #[inline]
    pub(crate) fn is_frozen(&self) -> bool {
        self.status_byte().load(Acquire) & FROZEN_BIT != 0
    }

    #[inline]
    pub(crate) fn is_retired(&self) -> bool {
        self.status_byte().load(Acquire) & RETIRED_BIT != 0
    }

    #[inline]
    pub(crate) fn freeze(&self) {
        let mut current = self.status_byte().load(Acquire);
        loop {
            let new = current | FROZEN_BIT;
            match self
                .status_byte()
                .compare_exchange(current, new, Release, Relaxed)
            {
                Ok(_) => break,
                Err(val) => current = val,
            }
        }
    }

    fn thaw(&self) {
        let mut current = self.status_byte().load(Acquire);
        loop {
            let new = current & !FROZEN_BIT;
            match self
                .status_byte()
                .compare_exchange(current, new, Release, Acquire)
            {
                Ok(_) => break,
                Err(actual) => current = actual,
            }
        }
    }

    #[inline]
    pub(crate) fn retire(&self) {
        let mut current = self.status_byte().load(Acquire);
        loop {
            let new = current | RETIRED_BIT;
            match self
                .status_byte()
                .compare_exchange(current, new, Release, Relaxed)
            {
                Ok(_) => break,
                Err(val) => current = val,
            }
        }
    }
}

impl<K: Ord, V> SimpleLeaf<K, V> {
    fn write(&self, index: usize, key: K, val: V) {
        unsafe {
            (*self.entry_array.get()).0[index].as_mut_ptr().write(key);
            (*self.entry_array.get()).1[index].as_mut_ptr().write(val);
        }
    }
    fn key_at(&self, index: usize) -> &K {
        unsafe { &*(*self.entry_array.get()).0[index].as_ptr() }
    }

    fn compare<Q>(&self, index: usize, key: &Q) -> Ordering
    where
        Q: Comparable<K> + ?Sized,
    {
        key.compare(self.key_at(index)).reverse()
    }

    fn search_slot<Q>(&self, key: &Q, ranks: &[u8; 8]) -> Option<usize>
    where
        Q: Comparable<K> + ?Sized,
    {
        let mut min_max_rank = REMOVED_RANK;
        let mut max_min_rank = 0;
        for i in 0..8 {
            let rank = ranks[i];
            if rank == UNINIT_RANK {
                continue;
            }
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
        }
        None
    }

    fn value_at(&self, index: usize) -> &V {
        unsafe { &*(*self.entry_array.get()).1[index].as_ptr() }
    }

    #[inline]
    pub(super) fn search_entry<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Comparable<K> + ?Sized,
    {
        // No need to load full metadata - search_slot handles individual loads
        let mut ranks = [0u8; 8];
        for i in 0..8 {
            ranks[i] = self.metadata[i].load(Acquire);
        }

        self.search_slot(key, &ranks)
            .map(|i| (self.key_at(i), self.value_at(i)))
    }
    fn take(&self, index: usize) -> (K, V) {
        unsafe {
            (
                (*self.entry_array.get()).0[index].as_ptr().read(),
                (*self.entry_array.get()).1[index].as_ptr().read(),
            )
        }
    }

    fn rollback(&self, index: usize) -> InsertResult<K, V> {
        let (key, val) = self.take(index);

        // Reset the entry's rank back to UNINIT_RANK
        self.metadata[index].store(UNINIT_RANK, Release);

        // Check status byte after rollback
        let status = self.status_byte().load(Acquire);
        if status & RETIRED_BIT != 0 {
            InsertResult::Retired(key, val)
        } else if status & FROZEN_BIT != 0 {
            InsertResult::Frozen(key, val)
        } else {
            InsertResult::Duplicate(key, val)
        }
    }

    fn post_insert(&self, free_slot_index: usize) -> InsertResult<K, V> {
        let key = self.key_at(free_slot_index);
        loop {
            // Add loop for retrying entire operation
            let mut min_max_rank = REMOVED_RANK;
            let mut max_min_rank = 0;
            let mut ranks_to_adjust = Vec::with_capacity(8);

            // First pass: find positions and collect all needed adjustments
            for i in 0..8 {
                let rank = self.metadata[i].load(Acquire);
                if rank == UNINIT_RANK {
                    continue;
                }
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
                            ranks_to_adjust.push((i, rank));
                        }
                        Ordering::Equal => {
                            return self.rollback(free_slot_index);
                        }
                    }
                }
            }

            let our_rank = max_min_rank + 1;

            // First set our rank
            match self.metadata[free_slot_index].compare_exchange(
                REMOVED_RANK,
                our_rank,
                Release,
                Acquire,
            ) {
                Ok(_) => {
                    // Now try to adjust all other ranks in their original state
                    let mut success = true;
                    for (i, original_rank) in ranks_to_adjust {
                        match self.metadata[i].compare_exchange(
                            original_rank, // Must still be in original state
                            original_rank + 1,
                            AcqRel,
                            Acquire,
                        ) {
                            Ok(_) => continue,
                            Err(_) => {
                                success = false;
                                break;
                            }
                        }
                    }

                    if success {
                        return InsertResult::Success;
                    } else {
                        return self.rollback(free_slot_index);
                    }
                }
                Err(_) => {
                    return self.rollback(free_slot_index);
                }
            }
        }
    }

    // Try to set our rank first
    fn try_freeze_for_insert(&self) -> bool {
        let mut current = self.status_byte().load(Acquire);
        loop {
            if current & (RETIRED_BIT | FROZEN_BIT) != 0 {
                return false;
            }
            match self.status_byte().compare_exchange(
                current,
                current | FROZEN_BIT,
                Acquire,
                Acquire,
            ) {
                Ok(_) => return true,
                Err(new) => current = new,
            }
        }
    }

    pub(super) fn insert(&self, key: K, val: V) -> InsertResult<K, V> {
        'retry: loop {
            if self.is_retired() {
                return InsertResult::Retired(key, val);
            } else if self.is_frozen() {
                return InsertResult::Frozen(key, val);
            }

            // Try to freeze for our insert
            if !self.try_freeze_for_insert() {
                continue 'retry;
            }

            // Do insert under frozen state
            let result = {
                for i in 0..8 {
                    let current = self.metadata[i].load(Acquire);
                    if current == UNINIT_RANK {
                        match self.metadata[i].compare_exchange(
                            UNINIT_RANK,
                            REMOVED_RANK,
                            Acquire,
                            Acquire,
                        ) {
                            Ok(_) => {
                                self.write(i, key, val);
                                let insert_result = self.post_insert(i);
                                self.thaw();
                                return insert_result;
                            }
                            Err(_) => {
                                self.thaw();
                                continue 'retry;
                            }
                        }
                    }
                }

                // No slots found
                let mut ranks = [0u8; 8];
                for i in 0..8 {
                    ranks[i] = self.metadata[i].load(Acquire);
                }
                self.thaw();
                if self.search_slot(&key, &ranks).is_some() {
                    return InsertResult::Duplicate(key, val);
                }
                return InsertResult::Full(key, val);
            };
        }
    }
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
    // #[inline]
    // pub(super) fn optimal_boundary(mut mutable_metadata: usize) -> usize {
    //     let mut boundary: usize = DIMENSION.num_entries;
    //     let mut prev_rank = 0;
    //     for _ in 0..DIMENSION.num_entries {
    //         let rank = mutable_metadata % (1_usize << DIMENSION.num_bits_per_entry);
    //         if rank != 0 && rank != DIMENSION.removed_rank() {
    //             if prev_rank >= rank {
    //                 boundary -= 1;
    //             } else if prev_rank != 0 {
    //                 boundary += 1;
    //             }
    //             prev_rank = rank;
    //         }
    //         mutable_metadata >>= DIMENSION.num_bits_per_entry;
    //     }
    //     boundary.clamp(
    //         DIMENSION.num_entries / 2 + 1,
    //         DIMENSION.num_entries + DIMENSION.num_entries / 2 - 1,
    //     ) - DIMENSION.num_entries / 2
    // }

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

        let entries: Vec<_> = Scanner {
            leaf: self,
            metadata,
            entry_index: DIMENSION.num_entries,
        }
        .collect();

        let split_point = (entries.len() + 1) / 2;

        for (i, (k, v)) in entries.into_iter().enumerate() {
            if i < split_point {
                low_key_leaf
                    .get_or_insert_with(|| Shared::new(Leaf::new()))
                    .insert_unchecked(k.clone(), v.clone(), i);
            } else {
                high_key_leaf
                    .get_or_insert_with(|| Shared::new(Leaf::new()))
                    .insert_unchecked(k.clone(), v.clone(), i - split_point);
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

/// Each constructed entry in an `EntryArray` is never dropped until the [`Leaf`] is dropped.
pub type EntryArray<K, V> = (
    [MaybeUninit<K>; DIMENSION.num_entries],
    [MaybeUninit<V>; DIMENSION.num_entries],
);

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

mod tests {
    use super::*;
    use std::sync::atomic::Ordering::*;

    #[test]
    fn test_scanner_ordering() {
        let leaf = Leaf::<i32, ()>::new();

        // Insert values in an order that would challenge rank assignment
        let values = [5, 3, 7, 1, 2, 4, 6];

        for &val in &values {
            match leaf.insert(val, ()) {
                InsertResult::Success => (),
                _ => panic!("Failed to insert {}", val),
            }
        }

        // Use Scanner to verify iteration order
        let scanner = Scanner::new(&leaf);
        let scanned: Vec<i32> = scanner.map(|(k, _)| *k).collect();

        // Values should come out in sorted order
        assert_eq!(
            &scanned,
            &[1, 2, 3, 4, 5, 6, 7],
            "Scanner didn't traverse in sorted order: {:?}",
            scanned
        );
    }

    #[test]
    fn test_leaf_operations() {
        let leaf = SimpleLeaf::<i32, ()>::new();
        // Add debug prints:
        for i in (0..8).rev() {
            println!("Inserting {}", i);
            let result = leaf.insert(i, ());
            // Print metadata after each insert
            assert!(matches!(result, InsertResult::Success));
        }

        for i in (0..8).rev() {
            println!("Searching {}", i);
            // Print metadata after each insert
            assert!(leaf.search_entry(&i).is_some(), "with: {}", i);
        }
    }

    #[test]
    fn test_leaf_edge_cases() {
        // Insert in different orders to test rank assignment
        let leaf = SimpleLeaf::<i32, ()>::new();

        // Test 1: Alternating high/low values
        let data = [0, 7, 1, 6, 2, 5, 3, 4];
        for &i in &data {
            assert!(matches!(leaf.insert(i, ()), InsertResult::Success));
        }
        // Verify order is maintained
        for i in 0..8 {
            assert!(leaf.search_entry(&i).is_some());
        }

        // Test 2: Duplicate handling
        let leaf = SimpleLeaf::<i32, ()>::new();
        assert!(matches!(leaf.insert(1, ()), InsertResult::Success));
        assert!(matches!(leaf.insert(1, ()), InsertResult::Duplicate(1, ())));

        // Test 3: Full leaf handling
        let leaf = SimpleLeaf::<i32, ()>::new();
        for i in 0..8 {
            assert!(matches!(leaf.insert(i, ()), InsertResult::Success));
        }
        assert!(matches!(leaf.insert(9, ()), InsertResult::Full(9, ())));

        // Test 4: Frozen/Retired states
        let leaf = SimpleLeaf::<i32, ()>::new();
        assert!(matches!(leaf.insert(1, ()), InsertResult::Success));
        leaf.freeze();
        assert!(matches!(leaf.insert(2, ()), InsertResult::Frozen(2, ())));
        leaf.retire();
        assert!(matches!(leaf.insert(3, ()), InsertResult::Retired(3, ())));

        // Test 5: Search in empty slots
        let leaf = SimpleLeaf::<i32, ()>::new();
        assert!(leaf.search_entry(&1).is_none());
    }

    #[test]
    fn test_rollback_scenarios() {
        let leaf = SimpleLeaf::<i32, ()>::new();

        // Insert some initial values
        assert!(matches!(leaf.insert(1, ()), InsertResult::Success));
        assert!(matches!(leaf.insert(3, ()), InsertResult::Success));

        // Test rollback during concurrent operations
        // (This might need to be modified based on how you simulate concurrency)
        leaf.freeze();
        let result = leaf.insert(2, ());
        assert!(matches!(result, InsertResult::Frozen(2, ())));

        // Verify state after rollback
        assert!(leaf.search_entry(&1).is_some());
        assert!(leaf.search_entry(&2).is_none());
        assert!(leaf.search_entry(&3).is_some());
    }

    #[test]
    fn test_rank_assignments() {
        let leaf = SimpleLeaf::<i32, ()>::new();

        // Insert in reverse order to force rank adjustments
        for i in (0..8).rev() {
            assert!(matches!(leaf.insert(i, ()), InsertResult::Success));
            // Check all previously inserted items are still findable
            for j in i..8 {
                assert!(
                    leaf.search_entry(&j).is_some(),
                    "Lost value {} after inserting {}",
                    j,
                    i
                );
            }
        }
    }

    #[test]
    fn test_mixed_operations() {
        let leaf = SimpleLeaf::<i32, ()>::new();

        // Mix of operations
        assert!(matches!(leaf.insert(5, ()), InsertResult::Success));
        assert!(leaf.search_entry(&5).is_some());
        assert!(matches!(leaf.insert(3, ()), InsertResult::Success));
        assert!(leaf.search_entry(&3).is_some());
        assert!(matches!(leaf.insert(7, ()), InsertResult::Success));
        assert!(leaf.search_entry(&7).is_some());

        // Verify ordering
        let values: Vec<i32> = (0..8)
            .filter_map(|i| leaf.search_entry(&i).map(|(k, _)| *k))
            .collect();
        assert!(
            values.windows(2).all(|w| w[0] < w[1]),
            "Values not properly ordered"
        );
    }

    #[test]
    fn test_concurrent_operations() {
        use std::collections::HashSet;
        use std::sync::atomic::AtomicUsize;
        use std::sync::Arc;
        use std::thread;

        let leaf = Arc::new(SimpleLeaf::<i32, ()>::new());
        let successful_inserts = Arc::new(AtomicUsize::new(0));
        let mut handles = vec![];

        // Track what values each thread attempted to insert
        let mut attempted_values = HashSet::new();

        // Spawn threads
        for i in 0..4 {
            let leaf_clone = Arc::clone(&leaf);
            let success_counter = Arc::clone(&successful_inserts);

            // Record attempted values
            attempted_values.insert(i * 2);
            attempted_values.insert(i * 2 + 1);

            handles.push(thread::spawn(move || {
                for j in 0..2 {
                    let val = i * 2 + j;
                    loop {
                        // Add loop to handle Retry
                        match leaf_clone.insert(val, ()) {
                            InsertResult::Success => {
                                success_counter.fetch_add(1, Relaxed);
                                break;
                            }
                            InsertResult::Full(..) => {
                                // Expected - leaf might be full
                                return;
                            }
                            InsertResult::Duplicate(..) => {
                                // Actually impossible in this test because each thread
                                // inserts unique values
                                panic!("Got duplicate when inserting unique value {}", val);
                            }
                            InsertResult::Retry(..)
                            | InsertResult::Frozen(..)
                            | InsertResult::Retired(..) => {
                                // Not expected in this test
                                continue;
                            }
                        }
                    }
                }
            }));
        }

        // Wait for all threads
        for handle in handles {
            handle.join().unwrap();
        }

        // Verify final state
        let mut found_values = HashSet::new();
        for i in 0..8 {
            if let Some((k, _)) = leaf.search_entry(&i) {
                found_values.insert(*k);
            }
        }

        // Verification
        println!("Attempted to insert: {:?}", attempted_values);
        println!("Successfully found: {:?}", found_values);
        println!("Reported successes: {}", successful_inserts.load(Relaxed));

        // Verify ordering
        let mut prev_opt = None;
        for i in 0..8 {
            if let Some((k, _)) = leaf.search_entry(&i) {
                if let Some(prev) = prev_opt {
                    assert!(*k > prev, "Values not properly ordered");
                }
                prev_opt = Some(*k);
            }
        }

        // Verify consistency between reported successes and found values
        assert_eq!(
            successful_inserts.load(Relaxed),
            found_values.len(),
            "Mismatch between reported successful inserts and found values"
        );

        // Verify we didn't exceed capacity
        assert!(
            found_values.len() <= 8,
            "More values present than leaf capacity"
        );

        // Verify all found values were from our attempt set
        for value in &found_values {
            assert!(
                attempted_values.contains(value),
                "Found value {} that wasn't attempted",
                value
            );
        }
    }
}
