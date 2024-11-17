use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::NodeLike;
use arc_swap::{ArcSwap, Guard};
use core::borrow::Borrow;
use core::iter::FusedIterator;
use core::ops::Bound;
use core::ops::RangeBounds;
use std::ops::Deref;
use std::sync::Arc;

/// A **persistent** concurrent ordered set based on a B-Tree.
///
/// See [`BTreeMap`]'s documentation for a detailed discussion of this collection's performance
/// benefits and drawbacks.
///
/// It is a logic error for an item to be modified in such a way that the item's ordering relative
/// to any other item, as determined by the [`Ord`] trait, changes while it is in the set. This is
/// normally only possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
/// The behavior resulting from such a logic error is not specified, but will be encapsulated to the
/// `BTreeSet` that observed the logic error and not result in undefined behavior. This could
/// include panics, incorrect results, aborts, memory leaks, and non-termination.
///
/// Iterators returned by [`crate::BTreeSet::iter`] produce their items in order, and take worst-case
/// logarithmic and amortized constant time per item returned.
///
/// [`Cell`]: crate::core::cell::Cell
/// [`RefCell`]: crate::core::cell::RefCell
///
/// # Examples
///
/// ```
/// use indexset::concurrent::set::BTreeSet;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `BTreeSet<&str>` in this example).
/// let mut books = BTreeSet::new();
///
/// // Add some books.
/// books.insert("A Dance With Dragons");
/// books.insert("To Kill a Mockingbird");
/// books.insert("The Odyssey");
/// books.insert("The Great Gatsby");
///
/// // Check for a specific one.
/// if !books.contains("The Winds of Winter") {
///     println!("We have {} books, but The Winds of Winter ain't one.",
///              books.len());
/// }
///
/// // Remove a book.
/// books.remove("The Odyssey");
///
/// // Iterate over everything.
/// for book in &books {
///     println!("{book}");
/// }
/// ```
///
/// A `BTreeSet` with a known list of items can be initialized from an array:
///
/// ```
/// use indexset::concurrent::set::BTreeSet;
///
/// let set = BTreeSet::from_iter([1, 2, 3]);
/// ```
#[derive(Debug)]
pub struct BTreeSet<T>
where
    T: Ord,
{
    node_capacity: usize,
    inner: ArcSwap<Vec<Arc<ArcSwap<Vec<T>>>>>,
}

impl<T: Ord> Default for BTreeSet<T> {
    fn default() -> Self {
        Self {
            node_capacity: DEFAULT_INNER_SIZE,
            inner: ArcSwap::from_pointee(vec![Arc::new(ArcSwap::from_pointee(
                Vec::with_capacity(DEFAULT_INNER_SIZE),
            ))]),
        }
    }
}

type FrozenBTree<T> = Vec<Arc<Vec<T>>>;

fn unfreeze<T: Ord + Clone>(snapshot: FrozenBTree<T>) -> Arc<Vec<Arc<ArcSwap<Vec<T>>>>> {
    Arc::new(
        snapshot
            .iter()
            .map(|node_snapshot| Arc::new(ArcSwap::new(node_snapshot.clone())))
            .collect(),
    )
}

fn freeze<T: Ord + Clone>(btree: &ArcSwap<Vec<Arc<ArcSwap<Vec<T>>>>>) -> FrozenBTree<T> {
    btree
        .load_full()
        .iter()
        .map(|node| node.load_full())
        .collect()
}

fn freeze_nodes<T: Ord + Clone>(
    partially_frozen_btree: &Arc<Vec<Arc<ArcSwap<Vec<T>>>>>,
) -> Vec<Arc<Vec<T>>> {
    partially_frozen_btree
        .iter()
        .map(|node_ref| node_ref.load_full())
        .collect()
}

fn locate_node<T: Ord, P, Q, K>(snapshot: K, mut cmp: P) -> (usize, Arc<Vec<T>>)
where
    K: Borrow<FrozenBTree<T>>,
    T: Borrow<Q>,
    Q: Ord + ?Sized,
    P: FnMut(&Q) -> bool,
{
    let snapshot = snapshot.borrow();

    let mut node_idx = snapshot.partition_point(|node| {
        if let Some(max) = node.last() {
            return cmp(max.borrow());
        }

        true
    });

    if snapshot.get(node_idx).is_none() {
        node_idx -= 1;
    }

    (node_idx, snapshot[node_idx].clone())
}

fn locate_value<T: Ord, P, Q>(snapshot: &FrozenBTree<T>, cmp: P) -> (Arc<Vec<T>>, usize)
where
    T: Borrow<Q>,
    Q: Ord + ?Sized,
    P: Fn(&Q) -> bool,
{
    let (_, node) = locate_node(snapshot, &cmp);
    let position_within_node = node.partition_point(|item| cmp(item.borrow()));

    (node, position_within_node)
}

fn locate_node_no_freezing<T: Ord, P, Q, K>(
    current_tree: K,
    mut cmp: P,
) -> (usize, Guard<Arc<Vec<T>>>)
where
    K: Borrow<ArcSwap<Vec<Arc<ArcSwap<Vec<T>>>>>>,
    T: Borrow<Q>,
    Q: Ord + ?Sized,
    P: FnMut(&Q) -> bool,
{
    let snapshot = current_tree.borrow().load();

    let mut node_idx = snapshot.partition_point(|node| {
        if let Some(max) = node.load().last() {
            return cmp(max.borrow());
        }

        true
    });

    if snapshot.get(node_idx).is_none() {
        node_idx -= 1;
    }

    (node_idx, snapshot.get(node_idx).unwrap().load())
}

fn locate_node_unsafe<T: Ord, P, Q, K>(
    partial_snapshot: K,
    mut cmp: P,
) -> (usize, Arc<ArcSwap<Vec<T>>>)
where
    K: Borrow<Arc<Vec<Arc<ArcSwap<Vec<T>>>>>>,
    T: Borrow<Q>,
    Q: Ord + ?Sized,
    P: FnMut(&Q) -> bool,
{
    let snapshot = partial_snapshot.borrow();

    let mut node_idx = snapshot.partition_point(|node| {
        if let Some(max) = node.load().last() {
            return cmp(max.borrow());
        }

        true
    });

    if snapshot.get(node_idx).is_none() {
        node_idx -= 1;
    }

    (node_idx, snapshot.get(node_idx).unwrap().clone())
}

fn locate_value_no_freezing<T: Ord, P, Q, K>(
    current_btree: K,
    cmp: P,
) -> (Guard<Arc<Vec<T>>>, usize)
where
    K: Borrow<ArcSwap<Vec<Arc<ArcSwap<Vec<T>>>>>>,
    T: Borrow<Q>,
    Q: Ord + ?Sized,
    P: Fn(&Q) -> bool,
{
    let (_, node) = locate_node_no_freezing(current_btree, &cmp);
    let position_within_node = node.partition_point(|item| cmp(item.borrow()));

    (node, position_within_node)
}

fn resolve_range<T, R>(
    snapshot: &FrozenBTree<T>,
    range: R,
) -> ((usize, usize, usize), (usize, usize, usize))
where
    R: RangeBounds<usize>,
{
    let mut global_front_idx: usize = 0;
    let mut global_back_idx: usize = snapshot
        .iter()
        .map(|xs| xs.len())
        .sum::<usize>()
        .saturating_sub(1);

    // Solving global indexes
    let start = range.start_bound();
    match start {
        Bound::Included(bound) => {
            global_front_idx = *bound;
        }
        Bound::Excluded(bound) => {
            global_front_idx = *bound + 1;
        }
        Bound::Unbounded => (),
    }

    let end = range.end_bound();
    match end {
        Bound::Included(bound) => {
            global_back_idx = *bound;
        }
        Bound::Excluded(bound) => {
            global_back_idx = *bound - 1;
        }
        Bound::Unbounded => (),
    }

    let (front_node_idx, front_start_idx) = locate_ith(snapshot, global_front_idx);
    let (back_node_idx, back_start_idx) = locate_ith(snapshot, global_back_idx);
    (
        (global_front_idx, front_node_idx, front_start_idx),
        (global_back_idx, back_node_idx, back_start_idx),
    )
}

fn range_idx<T, R>(btree: &BTreeSet<T>, range: R) -> Range<T>
where
    R: RangeBounds<usize>,
    T: Ord + Clone,
{
    let snapshot = freeze(&btree.inner);

    let (
        (global_front_idx, front_node_idx, front_start_idx),
        (global_back_idx, back_node_idx, back_start_idx),
    ) = resolve_range(&snapshot, range);

    let mut iter = Iter::new(Arc::new(snapshot));
    iter.current_front_node_idx = front_node_idx;
    iter.current_front_idx = global_front_idx;
    iter.current_back_node_idx = back_node_idx;
    iter.current_back_idx = global_back_idx + 1;

    let front_iter = if front_node_idx < iter.guards.len() {
        let front_node_size = iter.guards[front_node_idx].len();
        if front_start_idx < front_node_size {
            Some(unsafe {
                std::mem::transmute(iter.guards[front_node_idx][front_start_idx..].iter())
            })
        } else {
            None
        }
    } else {
        None
    };

    let back_iter = if back_node_idx < iter.guards.len() {
        let back_node_size = iter.guards[back_node_idx].len();
        if back_start_idx < back_node_size {
            Some(unsafe {
                std::mem::transmute(iter.guards[back_node_idx][..=back_start_idx].iter())
            })
        } else {
            None
        }
    } else {
        None
    };

    iter.current_front_iterator = front_iter;
    iter.current_back_iterator = back_iter;

    Range { iter }
}

fn rank<T, Q>(snapshot: &FrozenBTree<T>, value: &Q) -> usize
where
    Q: Ord + ?Sized,
    T: Borrow<Q> + Ord,
{
    let (mut node_idx, _) = locate_node(snapshot, |item| item < value);
    let (_node, position_within_node) = locate_value(snapshot, |item| item < value);
    let mut node_sizes: Vec<usize> = snapshot.iter().map(|xs| xs.len()).collect();
    node_sizes.insert(0, 0);
    let mut acc = 0;
    for x in &mut node_sizes {
        acc += *x;
        *x = acc;
    }

    if snapshot.get(node_idx).is_none() {
        node_idx -= 1;
    }

    node_sizes[node_idx] + position_within_node
}

fn locate_ith<T>(snapshot: &FrozenBTree<T>, idx: usize) -> (usize, usize) {
    let mut node_sizes: Vec<usize> = snapshot.iter().map(|xs| xs.len()).collect();
    node_sizes.insert(0, 0);
    let mut acc = 0;
    for x in &mut node_sizes {
        acc += *x;
        *x = acc;
    }

    let mut node_idx = node_sizes.partition_point(|node_size_cumsum| *node_size_cumsum < idx);

    //if snapshot.get(node_idx).is_none() {
    node_idx = node_idx.saturating_sub(1);
    //}

    (node_idx, idx.saturating_sub(node_sizes[node_idx]))
}

impl<T: Ord + Clone> BTreeSet<T> {
    /// Makes a new, empty, concurrent `BTreeSet`.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let set: BTreeSet<i32> = BTreeSet::new();
    /// ```
    pub fn new() -> Self {
        Self {
            ..Default::default()
        }
    }
    pub fn with_maximum_node_size(maximum_node_size: usize) -> Self {
        Self {
            node_capacity: maximum_node_size,
            inner: ArcSwap::from_pointee(vec![Arc::new(ArcSwap::from_pointee(
                Vec::with_capacity(maximum_node_size),
            ))]),
        }
    }
    pub(crate) fn get<P, Q, R, S>(&self, cmp: P, cmp2: R, mut f: S)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: Fn(&Q) -> bool,
        R: Fn(&T) -> bool,
        S: FnMut(&T),
    {
        let (expected_node, expected_place) = locate_value(&freeze(&self.inner), cmp);
        if let Some(candidate_value) = expected_node.get(expected_place) {
            if (&cmp2)(candidate_value) {
                f(candidate_value)
            }
        };
    }
    pub(crate) fn contains_cmp<P, Q, R>(&self, cmp: P, cmp2: R) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: Fn(&Q) -> bool,
        R: Fn(&T) -> bool,
    {
        let (expected_node, expected_place) = locate_value_no_freezing(&self.inner, cmp);
        if let Some(candidate_value) = expected_node.get(expected_place) {
            return (&cmp2)(candidate_value);
        };

        false
    }
    /// Returns `true` if the set contains an element equal to the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([1, 2, 3]);
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.contains_cmp(|item| item.borrow() < value, |item| item.borrow() == value)
    }
    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the set did not previously contain an equal value, `true` is
    ///   returned.
    /// - If the set already contained an equal value, `false` is returned, and
    ///   the entry is not updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&self, value: T) -> bool {
        let mut update = false;

        self.inner.rcu(|current_btree| {
            let mut new_snapshot = freeze_nodes(current_btree);
            let (node_idx, node_snapshot) = locate_node(&new_snapshot, |x| *x < value);
            let mut node = (*node_snapshot).clone();
            let local_value = value.clone();
            if node.len() < self.node_capacity {
                if NodeLike::insert(&mut node, local_value) {
                    update = true;

                    new_snapshot[node_idx] = Arc::new(node);
                }

                return unfreeze(new_snapshot.clone());
            }

            let mut new_node = node.halve();
            if value >= new_node[0] {
                if NodeLike::insert(&mut new_node, local_value) {
                    update = true;
                };
            } else {
                if NodeLike::insert(&mut node, local_value) {
                    update = true;
                }
            }

            new_snapshot[node_idx] = Arc::new(node);
            new_snapshot.insert(node_idx + 1, Arc::new(new_node));

            unfreeze(new_snapshot)
        });

        update
    }
    /// Adds a value to the set, under the assumption that the current thread is the only one
    /// that is currently inserting (no problems with readers though). Super unsafe, stay clear
    /// unless you know what you are doing.
    pub fn insert_spmc(&self, value: T) -> bool {
        let mut update = false;

        self.inner.rcu(|current_btree| {
            let (node_idx, node_snapshot) = locate_node_unsafe(current_btree, |x| *x < value);
            let local_value = value.clone();
            let node = node_snapshot.load_full();
            if node.len() < self.node_capacity {
                if !NodeLike::contains(node.as_ref(), &value) {
                    let mut node = (*node).clone();

                    NodeLike::insert(&mut node, local_value);
                    update = true;
                    current_btree[node_idx].store(Arc::new(node));
                };

                return current_btree.clone();
            }

            let mut node = (*node).clone();
            let mut new_node = node.halve();
            if value >= new_node[0] {
                if NodeLike::insert(&mut new_node, local_value) {
                    update = true;
                };
            } else {
                if NodeLike::insert(&mut node, local_value) {
                    update = true;
                }
            }

            let mut new_snapshot = (**current_btree).clone();
            new_snapshot[node_idx].store(Arc::new(node));
            new_snapshot.insert(node_idx + 1, Arc::new(ArcSwap::from_pointee(new_node)));

            Arc::new(new_snapshot)
        });

        update
    }
    // pub(crate) fn delete_cmp<Q, P, R>(&self, cmp: P, cmp2: R) -> (bool, Option<T>)
    // where
    //     T: Borrow<Q>,
    //     Q: Ord + ?Sized,
    //     P: Fn(&Q) -> bool,
    //     R: Fn(&T) -> bool,
    // {
    //     let mut update = false;
    //     let mut deleted_value = None;

    //     self.inner.rcu(|top_level| {
    //         let mut new_snapshot = freeze_nodes(top_level);

    //         let (node_idx, node_borrow) = locate_node(&new_snapshot, &cmp);

    //         let position_within_node = node_borrow.partition_point(|x| cmp(x.borrow()));
    //         if let Some(candidate_value) = node_borrow.get(position_within_node) {
    //             if !cmp2(candidate_value) {
    //                 return unfreeze(new_snapshot);
    //             }
    //         } else {
    //             return unfreeze(new_snapshot);
    //         }

    //         update = true;

    //         let mut node = (*node_borrow).clone();
    //         deleted_value = Some(node.delete(position_within_node));

    //         if node.len() == 0 {
    //             if new_snapshot.len() > 1 {
    //                 new_snapshot.remove(node_idx);

    //                 return unfreeze(new_snapshot);
    //             }
    //         };

    //         new_snapshot[node_idx] = Arc::new(node);

    //         unfreeze(new_snapshot)
    //     });

    //     (update, deleted_value)
    // }
    // pub(crate) fn delete<Q>(&self, value: &Q) -> (bool, Option<T>)
    // where
    //     T: Borrow<Q> + Ord,
    //     Q: Ord + ?Sized,
    // {
    //     self.delete_cmp(|x| x < value, |x| x.borrow() == value)
    // }
    /// If the set contains an element equal to the value, removes it from the
    /// set and drops it. Returns whether such an element was present.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    // pub fn remove<Q>(&self, value: &Q) -> bool
    // where
    //     T: Borrow<Q> + Ord,
    //     Q: Ord + ?Sized,
    // {
    //     self.delete(value).0
    // }
    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.load().iter().map(|node| node.load().len()).sum()
    }
    /// Gets an iterator that visits the elements in the `BTreeSet` in ascending
    /// order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([1, 2, 3]);
    /// let mut set_iter = set.iter();
    /// assert_eq!(set_iter.next(), Some(&1));
    /// assert_eq!(set_iter.next(), Some(&2));
    /// assert_eq!(set_iter.next(), Some(&3));
    /// assert_eq!(set_iter.next(), None);
    /// ```
    ///
    /// Values returned by the iterator are returned in ascending order:
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([3, 1, 2]);
    /// let mut set_iter = set.iter();
    /// assert_eq!(set_iter.next(), Some(&1));
    /// assert_eq!(set_iter.next(), Some(&2));
    /// assert_eq!(set_iter.next(), Some(&3));
    /// assert_eq!(set_iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(Arc::new(freeze(&self.inner)))
    }
    /// Constructs a double-ended iterator over a sub-range of elements in the set.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    /// use std::ops::Bound::Included;
    ///
    /// let mut set = BTreeSet::new();
    /// set.insert(3);
    /// set.insert(5);
    /// set.insert(8);
    /// for &elem in set.range((Included(&4), Included(&8))) {
    ///     println!("{elem}");
    /// }
    /// assert_eq!(Some(&5), set.range(4..).next());
    /// ```
    pub fn range<R, Q>(&self, range: R) -> Range<'_, T>
    where
        Q: Ord + ?Sized,
        T: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        let snapshot = Arc::new(freeze(&self.inner));

        let start_idx = match range.start_bound() {
            Bound::Included(bound) => rank(&snapshot, bound),
            Bound::Excluded(bound) => rank(&snapshot, bound) + 1,
            Bound::Unbounded => 0,
        };
        let end_idx = match range.end_bound() {
            Bound::Included(bound) => rank(&snapshot, bound),
            Bound::Excluded(bound) => rank(&snapshot, bound).saturating_sub(1),
            Bound::Unbounded => self.len().saturating_sub(1),
        };

        range_idx(&self, start_idx..=end_idx)
    }
    pub fn remove_range<R, Q>(&self, range: R)
    where
        Q: Ord + ?Sized,
        T: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        self.inner.rcu(|top_level| {
            let mut snapshot = freeze_nodes(top_level);

            let start_idx = match range.start_bound() {
                Bound::Included(bound) => rank(&snapshot, bound),
                Bound::Excluded(bound) => rank(&snapshot, bound) + 1,
                Bound::Unbounded => 0,
            };
            let end_idx = match range.end_bound() {
                Bound::Included(bound) => rank(&snapshot, bound),
                Bound::Excluded(bound) => rank(&snapshot, bound).saturating_sub(1),
                Bound::Unbounded => self.len().saturating_sub(1),
            };

            let (
                (_global_front_idx, front_node_idx, front_start_idx),
                (_global_back_idx, back_node_idx, back_start_idx),
            ) = resolve_range(&snapshot, start_idx..=end_idx);

            let mut empty_front = false;
            let mut empty_back = false;

            let number_of_nodes_to_be_popped = back_node_idx - front_node_idx;
            if number_of_nodes_to_be_popped == 0 {
                let front_node_size = snapshot[front_node_idx].len();
                if front_start_idx < front_node_size {
                    let mut front_node_copy = (*snapshot[front_node_idx]).clone();
                    front_node_copy.drain(front_start_idx..=back_start_idx);

                    if front_node_copy.len() == 0 {
                        empty_front = true
                    }
                    snapshot[front_node_idx] = Arc::new(front_node_copy);
                }
            } else {
                if front_node_idx < snapshot.len() {
                    let front_node_size = snapshot[front_node_idx].len();
                    if front_start_idx < front_node_size {
                        let mut front_node_copy = (*snapshot[front_node_idx]).clone();
                        front_node_copy.drain(front_start_idx..);

                        if front_node_copy.len() == 0 {
                            empty_front = true;
                        }
                        snapshot[front_node_idx] = Arc::new(front_node_copy);
                    }
                };

                if back_node_idx < snapshot.len() {
                    let back_node_size = snapshot[back_node_idx].len();
                    if back_start_idx < back_node_size {
                        let mut back_node_copy = (*snapshot[back_node_idx]).clone();
                        back_node_copy.drain(0..=back_start_idx);

                        if back_node_copy.len() == 0 {
                            empty_back = true;
                        }
                        snapshot[back_node_idx] = Arc::new(back_node_copy);
                    }
                };

                if number_of_nodes_to_be_popped > 1 {
                    for _ in 0..number_of_nodes_to_be_popped {
                        snapshot.remove(front_node_idx + 1);
                    }
                }
            }

            if empty_front && snapshot.len() > 1 {
                snapshot.remove(front_node_idx);
            }

            if empty_back && snapshot.len() > 1 {
                if number_of_nodes_to_be_popped > 1 {
                    if empty_front {
                        snapshot.remove(front_node_idx);
                    } else {
                        snapshot.remove(front_node_idx + 1);
                    }
                } else {
                    snapshot.remove(back_node_idx);
                }
            }

            unfreeze(snapshot)
        });
    }
}

impl<T, const N: usize> From<[T; N]> for BTreeSet<T>
where
    T: Ord + Clone,
{
    fn from(value: [T; N]) -> Self {
        let btree: BTreeSet<T> = Default::default();

        value.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

impl<T> FromIterator<T> for BTreeSet<T>
where
    T: Ord + Clone,
{
    fn from_iter<K: IntoIterator<Item = T>>(iter: K) -> Self {
        let btree = BTreeSet::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

/// An iterator over the items of a `BTreeSet`.
///
/// This `struct` is created by the [`iter`] method on [`crate::concurrent::set::BTreeSet`].
/// See its documentation for more.
///
/// [`iter`]: crate::concurrent::set::BTreeSet::iter
pub struct Iter<'a, T: 'a>
where
    T: Ord + 'a,
{
    guards: Arc<Vec<Arc<Vec<T>>>>,
    current_front_node_idx: usize,
    current_front_idx: usize,
    current_back_node_idx: usize,
    current_back_idx: usize,
    current_front_iterator: Option<std::slice::Iter<'a, T>>,
    current_back_iterator: Option<std::slice::Iter<'a, T>>,
}

impl<'a, T> Iter<'a, T>
where
    T: Ord,
{
    pub fn new(guards: Arc<Vec<Arc<Vec<T>>>>) -> Self {
        let node_count = guards.len();
        let front_iter = if node_count > 0 {
            Some(unsafe { std::mem::transmute(guards[0].iter()) })
        } else {
            None
        };
        let back_iter = if node_count > 0 {
            Some(unsafe { std::mem::transmute(guards[node_count - 1].iter()) })
        } else {
            None
        };

        let element_count: usize = guards.iter().map(|xs| xs.len()).sum();

        Self {
            guards,
            current_front_node_idx: 0,
            current_front_idx: 0,
            current_back_node_idx: node_count.saturating_sub(1),
            current_back_idx: element_count,
            current_front_iterator: front_iter,
            current_back_iterator: back_iter,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: Ord + Clone,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_front_idx == self.current_back_idx {
            return None;
        }

        if let Some(value) = self.current_front_iterator.as_mut().and_then(|i| i.next()) {
            self.current_front_idx += 1;

            Some(value)
        } else {
            self.current_front_node_idx += 1;

            if self.current_front_node_idx >= self.guards.len() {
                return None;
            }

            self.current_front_iterator = Some(unsafe {
                std::mem::transmute(self.guards[self.current_front_node_idx].iter())
            });

            self.next()
        }
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T>
where
    T: Ord + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.current_front_idx == self.current_back_idx {
            return None;
        }
        if let Some(value) = self
            .current_back_iterator
            .as_mut()
            .and_then(|i| i.next_back())
        {
            self.current_back_idx -= 1;
            Some(value)
        } else {
            if self.current_back_node_idx == 0 {
                return None;
            };
            self.current_back_node_idx -= 1;
            self.current_back_iterator = Some(unsafe {
                std::mem::transmute(self.guards[self.current_back_node_idx].iter())
            });

            self.next_back()
        }
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> where T: Ord + Clone {}

impl<'a, T> IntoIterator for &'a BTreeSet<T>
where
    T: Ord + Clone,
{
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        let guards = Arc::new(freeze(&self.inner));

        Iter::new(guards)
    }
}

/// An iterator over a sub-range of items in a `BTreeSet`.
///
/// This `struct` is created by the [`range`] method on [`crate::concurrent::set::BTreeSet`].
/// See its documentation for more.
///
/// [`range`]: crate::concurrent::set::BTreeSet::range
pub struct Range<'a, T>
where
    T: Ord + Clone,
{
    iter: Iter<'a, T>,
}

impl<'a, T> Iterator for Range<'a, T>
where
    T: Ord + Clone,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T> DoubleEndedIterator for Range<'a, T>
where
    T: Ord + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<'a, T> FusedIterator for Range<'a, T> where T: Ord + Clone {}

// #[cfg(test)]
// mod tests {
//     use crate::concurrent::set::BTreeSet;
//     use crate::core::constants::DEFAULT_INNER_SIZE;
//     use rand::Rng;
//     use std::collections::Bound::{Excluded, Included};
//     use std::collections::HashSet;
//     use std::sync::Arc;
//     use std::thread;

//     #[test]
//     fn test_concurrent_insert() {
//         let set = Arc::new(BTreeSet::<i32>::new());
//         let num_threads = 8;
//         let operations_per_thread = 1000;

//         let mut handles = vec![];
//         let mut thread_local_data = Arc::new(vec![]);
//         let mut expected_len = HashSet::new();
//         for _ in 0usize..num_threads {
//             let mut data = vec![];
//             let mut rng = rand::thread_rng();
//             for _ in 0..operations_per_thread {
//                 let value = rng.gen_range(0..10000);
//                 let operation = rng.gen_range(0..2);
//                 if operation == 0 {
//                     expected_len.insert(value);
//                 };

//                 data.push((operation, value))
//             }

//             let mut new_tld = (*thread_local_data).clone();
//             new_tld.push(data);

//             thread_local_data = Arc::new(new_tld)
//         }

//         for thread_idx in 0usize..num_threads {
//             let set_clone = Arc::clone(&set);
//             let local_tld = thread_local_data.clone();
//             let handle = thread::spawn(move || {
//                 for op_idx in 0usize..operations_per_thread {
//                     let (operation, value) = &local_tld[thread_idx][op_idx];

//                     if *operation == 0 {
//                         set_clone.insert(value.clone());
//                     }
//                 }
//             });
//             handles.push(handle);
//         }

//         for handle in handles {
//             handle.join().unwrap();
//         }

//         assert_eq!(set.len(), expected_len.len());

//         for thread_idx in 0usize..num_threads {
//             for op_idx in 0usize..operations_per_thread {
//                 let (op, value) = thread_local_data[thread_idx][op_idx];
//                 if op == 0 {
//                     assert!(set.contains(&value))
//                 }
//             }
//         }
//     }
//     #[test]
//     fn test_insert_spmc() {
//         let set = Arc::new(BTreeSet::<i32>::new());
//         let range = (0..100_000);
//         for i in range {
//             set.insert_spmc(i);
//         }

//         assert_eq!(set.len(), 100_000);
//         for i in 0..100_000 {
//             set.contains(&i);
//         }
//     }

//     #[test]
//     fn test_remove_single_element() {
//         let set = BTreeSet::<i32>::new();
//         set.insert(5);
//         assert!(set.contains(&5));
//         assert!(set.remove(&5));
//         assert!(!set.contains(&5));
//         assert!(!set.remove(&5));
//     }

//     #[test]
//     fn test_remove_multiple_elements() {
//         let set = BTreeSet::<i32>::new();
//         for i in 0..100 {
//             set.insert(i);
//         }
//         for i in 0..100 {
//             assert!(set.remove(&i));
//             assert!(!set.contains(&i));
//         }
//         assert_eq!(set.len(), 0);
//     }

//     #[test]
//     fn test_remove_non_existent() {
//         let set = BTreeSet::<i32>::new();
//         set.insert(5);
//         assert!(!set.remove(&10));
//         assert!(set.contains(&5));
//     }
//     #[test]
//     fn test_remove_stress() {
//         let set = Arc::new(BTreeSet::<i32>::new());
//         const NUM_ELEMENTS: i32 = 10000;

//         for i in 0..NUM_ELEMENTS {
//             assert!(set.insert(i), "Failed to insert {}", i);
//         }
//         assert_eq!(
//             set.len(),
//             NUM_ELEMENTS as usize,
//             "Incorrect size after insertion"
//         );

//         let num_threads = 8;
//         let elements_per_thread = NUM_ELEMENTS / num_threads;
//         let handles: Vec<_> = (0..num_threads)
//             .map(|t| {
//                 let set = Arc::clone(&set);
//                 thread::spawn(move || {
//                     for i in (t * elements_per_thread)..((t + 1) * elements_per_thread) {
//                         if i % 2 == 1 {
//                             assert!(set.remove(&i), "Failed to remove {}", i);
//                         }
//                     }
//                 })
//             })
//             .collect();

//         for handle in handles {
//             handle.join().unwrap();
//         }

//         assert_eq!(
//             set.len(),
//             NUM_ELEMENTS as usize / 2,
//             "Incorrect size after removal"
//         );

//         for i in 0..NUM_ELEMENTS {
//             if i % 2 == 0 {
//                 assert!(set.contains(&i), "Even number {} should be in the set", i);
//             } else {
//                 assert!(
//                     !set.contains(&i),
//                     "Odd number {} should not be in the set",
//                     i
//                 );
//             }
//         }
//     }

//     #[test]
//     fn test_remove_all_elements() {
//         let set = BTreeSet::<i32>::new();
//         let n = 1000;

//         for i in 0..n {
//             set.insert(i);
//         }

//         for i in 0..n {
//             assert!(set.remove(&i), "Failed to remove {}", i);
//         }

//         assert_eq!(set.len(), 0, "Set should be empty");

//         for i in 0..n {
//             assert!(!set.contains(&i), "Element {} should not be in the set", i);
//         }
//     }

//     #[test]
//     fn test_single_element() {
//         let set = BTreeSet::new();
//         set.insert(1);
//         let mut iter = set.into_iter();
//         assert_eq!(iter.next(), Some(&1));
//         assert_eq!(iter.next(), None);
//         assert_eq!(iter.next_back(), None);
//     }

//     #[test]
//     fn test_multiple_elements() {
//         let set = BTreeSet::new();
//         set.insert(1);
//         set.insert(2);
//         set.insert(3);
//         let mut iter = set.into_iter();
//         assert_eq!(iter.next(), Some(&1));
//         assert_eq!(iter.next_back(), Some(&3));
//         assert_eq!(iter.next(), Some(&2));
//         assert_eq!(iter.next(), None);
//         assert_eq!(iter.next_back(), None);
//     }

//     #[test]
//     fn test_bidirectional_iteration() {
//         let set = BTreeSet::new();
//         for i in 1..=100 {
//             set.insert(i);
//         }
//         let mut iter = set.into_iter();
//         for i in 1..=50 {
//             assert_eq!(iter.next(), Some(&i));
//             assert_eq!(iter.next_back(), Some(&(101 - i)));
//         }
//         assert_eq!(iter.next(), None);
//         assert_eq!(iter.next_back(), None);
//     }

//     #[test]
//     fn test_fused_iterator() {
//         let set = BTreeSet::new();
//         set.insert(1);
//         let mut iter = set.into_iter();
//         assert_eq!(iter.next(), Some(&1));
//         assert_eq!(iter.next(), None);
//         assert_eq!(iter.next(), None);
//     }

//     #[test]
//     fn test_large_set() {
//         let set = BTreeSet::new();
//         for i in 0..10000 {
//             set.insert(i);
//         }
//         assert_eq!(set.into_iter().count(), 10000);
//     }

//     #[test]
//     fn test_iterator_after_modifications() {
//         let set = BTreeSet::new();
//         for i in 0..100 {
//             set.insert(i);
//         }
//         let mut iter = set.into_iter();
//         assert_eq!(iter.next(), Some(&0));
//         set.insert(100); // This shouldn't affect the existing iterator
//         for i in 1..100 {
//             assert_eq!(iter.next(), Some(&i));
//         }
//         assert_eq!(iter.next(), None); // The new 100 shouldn't be visible
//     }

//     #[test]
//     fn test_out_of_bounds_range() {
//         let btree: BTreeSet<usize> = BTreeSet::from_iter(0..10);
//         assert_eq!(btree.range((Included(5), Included(10))).count(), 5);
//         assert_eq!(btree.range((Included(5), Included(11))).count(), 5);
//         assert_eq!(
//             btree
//                 .range((Included(5), Included(10 + DEFAULT_INNER_SIZE)))
//                 .count(),
//             5
//         );
//         assert_eq!(btree.range((Included(0), Included(11))).count(), 10);
//     }

//     #[test]
//     fn test_iterating_over_blocks() {
//         let btree = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE + 10)).into_iter());
//         assert_eq!(btree.iter().count(), (0..(DEFAULT_INNER_SIZE + 10)).count());
//         assert_eq!(
//             btree.range(0..DEFAULT_INNER_SIZE).count(),
//             (0..DEFAULT_INNER_SIZE).count()
//         );
//         assert_eq!(
//             btree.range(0..=DEFAULT_INNER_SIZE).count(),
//             (0..=DEFAULT_INNER_SIZE).count()
//         );
//         assert_eq!(
//             btree.range(0..=DEFAULT_INNER_SIZE + 1).count(),
//             (0..=DEFAULT_INNER_SIZE + 1).count()
//         );

//         assert_eq!(
//             btree.iter().rev().count(),
//             (0..(DEFAULT_INNER_SIZE + 10)).count()
//         );
//         assert_eq!(
//             btree.range(0..DEFAULT_INNER_SIZE).rev().count(),
//             (0..DEFAULT_INNER_SIZE).count()
//         );
//         assert_eq!(
//             btree.range(0..=DEFAULT_INNER_SIZE).rev().count(),
//             (0..=DEFAULT_INNER_SIZE).count()
//         );
//         assert_eq!(
//             btree.range(0..=DEFAULT_INNER_SIZE + 1).rev().count(),
//             (0..=DEFAULT_INNER_SIZE + 1).count()
//         );
//     }

//     #[test]
//     fn test_empty_set() {
//         let btree: BTreeSet<usize> = BTreeSet::new();
//         assert_eq!(btree.iter().count(), 0);
//         assert_eq!(btree.range(0..0).count(), 0);
//         assert_eq!(btree.range(0..).count(), 0);
//         assert_eq!(btree.range(..0).count(), 0);
//         assert_eq!(btree.range(..).count(), 0);
//         assert_eq!(btree.range(0..=0).count(), 0);
//         assert_eq!(btree.range(..1).count(), 0);

//         assert_eq!(btree.iter().rev().count(), 0);
//         assert_eq!(btree.range(0..0).rev().count(), 0);
//         assert_eq!(btree.range(..).rev().count(), 0);
//         assert_eq!(btree.range(..1).rev().count(), 0);

//         assert_eq!(btree.range(..DEFAULT_INNER_SIZE).count(), 0);
//         assert_eq!(
//             btree
//                 .range(DEFAULT_INNER_SIZE..DEFAULT_INNER_SIZE * 2)
//                 .count(),
//             0
//         );
//     }

//     #[test]
//     fn test_remove_range() {
//         let btree = BTreeSet::from_iter(0..=(DEFAULT_INNER_SIZE * 2));

//         btree.remove_range(5..15);
//         let expected_len = (DEFAULT_INNER_SIZE * 2) - 9;
//         let actual_len = btree.len();
//         assert_eq!(expected_len, actual_len);

//         btree.remove_range(DEFAULT_INNER_SIZE - 5..DEFAULT_INNER_SIZE + 5);
//         let expected_len = expected_len - 10;
//         let actual_len = btree.len();
//         assert_eq!(expected_len, actual_len);

//         btree.remove_range(..DEFAULT_INNER_SIZE / 2);
//         let expected_len = expected_len - ((DEFAULT_INNER_SIZE / 2) - 10);
//         let actual_len = btree.len();
//         assert_eq!(expected_len, actual_len);

//         btree.remove_range(DEFAULT_INNER_SIZE * 3 / 2..);
//         let expected_len =
//             expected_len - ((DEFAULT_INNER_SIZE * 2) - ((DEFAULT_INNER_SIZE * 3) / 2) + 1);
//         let actual_len = btree.len();
//         assert_eq!(expected_len, actual_len);

//         btree.remove_range(..);
//         assert_eq!(btree.len(), 0);

//         for i in 0..=(DEFAULT_INNER_SIZE * 2) {
//             btree.insert(i);
//         }

//         btree.remove_range((Excluded(5), Excluded(15)));
//         assert_eq!(
//             btree.range(0..DEFAULT_INNER_SIZE).count(),
//             DEFAULT_INNER_SIZE - 9
//         );

//         btree.remove_range((
//             Included(DEFAULT_INNER_SIZE),
//             Excluded(DEFAULT_INNER_SIZE + 10),
//         ));
//         assert_eq!(
//             btree.range(0..=DEFAULT_INNER_SIZE * 2).count(),
//             DEFAULT_INNER_SIZE * 2 - 18
//         );

//         let original_count = btree.len();
//         btree.remove_range(DEFAULT_INNER_SIZE * 3..DEFAULT_INNER_SIZE * 4);
//         assert_eq!(btree.len(), original_count);

//         btree.remove_range(DEFAULT_INNER_SIZE * 2 - 5..DEFAULT_INNER_SIZE * 3);
//         assert_eq!(btree.len(), original_count - 6);
//     }
// }
