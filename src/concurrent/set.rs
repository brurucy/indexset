use crossbeam_skiplist::SkipMap;
use crossbeam_utils::sync::ShardedLock;
use parking_lot::{ArcMutexGuard, Mutex, RawMutex};
use std::fmt::Debug;
use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};
#[cfg(feature = "cdc")]
use std::sync::atomic::{AtomicU64, Ordering};
use std::{borrow::Borrow, sync::Arc};

use crate::cdc::change::ChangeEvent;
use crate::concurrent::operation::*;
use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

use super::r#ref::Ref;

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
/// let mut books = BTreeSet::<&str>::new();
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
pub struct BTreeSet<T, Node = Vec<T>>
where
    T: Ord + Clone + 'static,
    Node: NodeLike<T>,
{
    pub(crate) index: SkipMap<T, Arc<Mutex<Node>>>,
    index_lock: ShardedLock<()>,
    node_capacity: usize,
    #[cfg(feature = "cdc")]
    event_id: AtomicU64,
}
impl<T: Ord + Clone + 'static, Node: NodeLike<T>> Default for BTreeSet<T, Node> {
    fn default() -> Self {
        let index = SkipMap::new();

        Self {
            index,
            index_lock: ShardedLock::new(()),
            node_capacity: DEFAULT_INNER_SIZE,
            #[cfg(feature = "cdc")]
            event_id: AtomicU64::new(0),
        }
    }
}

impl<T, Node> BTreeSet<T, Node>
where
    T: Debug + Ord + Clone + Send,
    Node: NodeLike<T> + Send + 'static,
{
    pub fn new() -> Self {
        Self::default()
    }
    /// Makes a new, empty `BTreeSet` with the given maximum node size. Allocates one vec with
    /// the capacity set to be the specified node size.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::concurrent::set::BTreeSet;
    ///
    /// let set: BTreeSet<i32> = BTreeSet::with_maximum_node_size(128);
    pub fn with_maximum_node_size(node_capacity: usize) -> Self {
        Self {
            index: SkipMap::new(),
            index_lock: ShardedLock::new(()),
            node_capacity,
            #[cfg(feature = "cdc")]
            event_id: AtomicU64::new(0),
        }
    }
    pub fn attach_node(&self, node: Node) {
        let node_id = node
            .max()
            .cloned()
            .expect("node should contain at least one value to be correct node");
        let _global_guard = self.index_lock.write();
        self.index.insert(node_id, Arc::new(Mutex::new(node)));
    }

    pub(crate) fn put_cdc_checked(
        &self,
        value: T,
    ) -> Result<(Option<T>, Vec<ChangeEvent<T>>), (ArcMutexGuard<RawMutex, Node>, usize, T)> {
        loop {
            let mut cdc = vec![];
            let _global_guard = self.index_lock.read();
            let target_node_entry = match self.index.lower_bound(std::ops::Bound::Included(&value))
            {
                Some(entry) => entry,
                None => {
                    if let Some(last) = self.index.back() {
                        last
                    } else {
                        let mut first_node = Node::with_capacity(self.node_capacity);

                        first_node.insert(value.clone());

                        let first_node = Arc::new(Mutex::new(first_node));

                        drop(_global_guard);
                        if let Ok(_) = self.index_lock.try_write() {
                            #[cfg(feature = "cdc")]
                            {
                                let node_insertion = ChangeEvent::CreateNode {
                                    // is correct as index is locked and current thread is the only that can
                                    // fetch event_id.
                                    event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                                    max_value: value.clone(),
                                };
                                cdc.push(node_insertion);
                            }

                            self.index.insert(value, first_node);

                            return Ok((None, cdc));
                        }

                        continue;
                    }
                }
            };

            let mut node_guard = target_node_entry.value().lock_arc();

            #[allow(unused_assignments)]
            let mut operation = None;
            #[cfg(feature = "cdc")]
            let mut operation_id = 0.into();
            if !node_guard.need_to_split(self.node_capacity, &value) {
                let old_max = node_guard.max().cloned();
                let (inserted, idx) = NodeLike::insert(&mut *node_guard, value.clone());
                if inserted {
                    #[cfg(feature = "cdc")]
                    {
                        let node_element_insertion = ChangeEvent::InsertAt {
                            // is correct as node is locked and current thread is the only that can
                            // fetch event_id, so events for this node will have monotonic id's.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: old_max.clone().unwrap_or(value.clone()),
                            value: value.clone(),
                            index: idx,
                        };
                        cdc.push(node_element_insertion);
                    }

                    if node_guard.max().cloned() == old_max {
                        return Ok((None, cdc));
                    }

                    if old_max.is_some() {
                        operation = Some(Operation::UpdateMax(
                            target_node_entry.value().clone(),
                            old_max.unwrap(),
                        ))
                    } else {
                        return Ok((None, cdc));
                    }
                } else {
                    return Err((node_guard, idx, old_max.unwrap()));
                }
            } else {
                operation = Some(Operation::Split(
                    target_node_entry.value().clone(),
                    target_node_entry.key().clone(),
                    value.clone(),
                ));
                #[cfg(feature = "cdc")]
                {
                    operation_id = self.event_id.fetch_add(1, Ordering::Relaxed).into();
                }
            }

            drop(node_guard);
            drop(_global_guard);

            let _global_guard = self.index_lock.write();

            let op = operation.unwrap();
            match &op {
                Operation::Split(_, _, _) => {
                    if let Ok((value, value_cdc)) = op.commit(
                        &self.index,
                        #[cfg(feature = "cdc")]
                        operation_id,
                    ) {
                        cdc.extend(value_cdc);
                        return Ok((value, cdc));
                    } else {
                        continue;
                    }
                }
                Operation::UpdateMax(_, _) => {
                    return if let Ok((value, value_cdc)) = op.commit(
                        &self.index,
                        #[cfg(feature = "cdc")]
                        operation_id,
                    ) {
                        cdc.extend(value_cdc);
                        Ok((value, cdc))
                    } else {
                        Ok((None, cdc))
                    }
                }
                Operation::MakeUnreachable(_, _) => unreachable!(),
            }
        }
    }
    pub(crate) fn put_cdc(&self, value: T) -> (Option<T>, Vec<ChangeEvent<T>>) {
        match self.put_cdc_checked(value.clone()) {
            Ok(res) => res,
            Err((mut node_guard, idx, max)) => {
                let mut cdc = vec![];
                #[cfg(feature = "cdc")]
                {
                    if node_guard.len() == 1 {
                        let node_removal = ChangeEvent::RemoveNode {
                            // is correct as node is locked and current thread is the only that can
                            // fetch event_id, so events for this node will have monotonic id's.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: max.clone(),
                        };
                        let node_insertion = ChangeEvent::CreateNode {
                            // same as for previous.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: value.clone(),
                        };
                        cdc.push(node_removal);
                        cdc.push(node_insertion);
                    } else if idx == node_guard.len() - 1 {
                        let new_max = if node_guard.len() <= 1 {
                            None
                        } else {
                            node_guard.get_ith(node_guard.len() - 2)
                        };
                        let node_element_removal = ChangeEvent::RemoveAt {
                            // is correct as node is locked and current thread is the only that can
                            // fetch event_id, so events for this node will have monotonic id's.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: max.clone(),
                            value: value.clone(),
                            index: idx,
                        };
                        let node_element_insertion = ChangeEvent::InsertAt {
                            // same as for previous.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: new_max.expect("length was checked so should be ok").clone(),
                            value: value.clone(),
                            index: idx,
                        };
                        cdc.push(node_element_removal);
                        cdc.push(node_element_insertion);
                    } else {
                        let node_element_removal = ChangeEvent::RemoveAt {
                            // is correct as node is locked and current thread is the only that can
                            // fetch event_id, so events for this node will have monotonic id's.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: max.clone(),
                            value: value.clone(),
                            index: idx,
                        };
                        let node_element_insertion = ChangeEvent::InsertAt {
                            // same as for previous.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: max.clone(),
                            value: value.clone(),
                            index: idx,
                        };
                        cdc.push(node_element_removal);
                        cdc.push(node_element_insertion);
                    }
                }

                (NodeLike::replace(&mut *node_guard, idx, value.clone()), cdc)
            }
        }
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
    /// let mut set = BTreeSet::<usize>::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&self, value: T) -> bool {
        if let (None, _) = self.put_cdc(value) {
            return true;
        }

        false
    }
    pub fn remove_cdc<Q>(&self, value: &Q) -> (Option<T>, Vec<ChangeEvent<T>>)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        loop {
            let mut cdc = vec![];
            let _global_guard = self.index_lock.read();
            if let Some(target_node_entry) =
                self.index.lower_bound(std::ops::Bound::Included(&value))
            {
                let mut node_guard = target_node_entry.value().lock_arc();
                let old_max = node_guard.max().cloned();
                let deleted = NodeLike::delete(&mut *node_guard, value);
                if deleted.is_none() {
                    return (None, cdc);
                }
                let (deleted, idx) = deleted.expect("should be ok as checked before");

                let operation = if node_guard.len() > 0 {
                    #[cfg(feature = "cdc")]
                    {
                        let node_element_removal = ChangeEvent::RemoveAt {
                            // is correct as node is locked and current thread is the only that can
                            // fetch event_id, so events for this node will have monotonic id's.
                            event_id: self.event_id.fetch_add(1, Ordering::Relaxed).into(),
                            max_value: old_max
                                .clone()
                                .expect("Max value should exist as Node is not empty"),
                            value: deleted.clone(),
                            index: idx,
                        };
                        cdc.push(node_element_removal);
                    }

                    if old_max.as_ref() == node_guard.max() {
                        return (Some(deleted), cdc);
                    }

                    Some(Operation::UpdateMax(
                        target_node_entry.value().clone(),
                        old_max.unwrap(),
                    ))
                } else {
                    Some(Operation::MakeUnreachable(
                        target_node_entry.value().clone(),
                        old_max.unwrap(),
                    ))
                };

                #[cfg(feature = "cdc")]
                let operation_id = self.event_id.fetch_add(1, Ordering::Relaxed).into();

                drop(node_guard);
                drop(_global_guard);

                let _global_guard = self.index_lock.write();

                return if let Ok((_, value_cdc)) = operation.unwrap().commit(
                    &self.index,
                    #[cfg(feature = "cdc")]
                    operation_id,
                ) {
                    cdc.extend(value_cdc);
                    (Some(deleted), cdc)
                } else {
                    (Some(deleted), cdc)
                };
            }

            break;
        }

        (None, vec![])
    }
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
    /// let mut set = BTreeSet::<usize>::new();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2).is_some(), true);
    /// assert_eq!(set.remove(&2).is_some(), false);
    /// ```
    pub fn remove<Q>(&self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.remove_cdc(value).0
    }
    fn locate_node<Q>(&self, value: &Q) -> Option<Arc<Mutex<Node>>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let _global_guard = self.index_lock.read();
        match self.index.lower_bound(std::ops::Bound::Included(&value)) {
            Some(entry) => Some(entry.value().clone()),
            None => self
                .index
                .back()
                .map(|last| last.value().clone())
                .or_else(|| self.index.front().map(|first| first.value().clone())),
        }
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
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(node) = self.locate_node(value) {
            return node.lock().contains(value);
        }

        false
    }
    pub fn get<'a, Q>(&'a self, value: &'a Q) -> Option<Ref<T, Node>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(node) = self.locate_node(value) {
            let node_guard = node.lock_arc();
            let potential_position = node_guard.try_select(value);

            if let Some(position) = potential_position {
                return Some(Ref {
                    node_guard,
                    position,
                    phantom_data: PhantomData,
                });
            }
        }

        None
    }
    pub fn len(&self) -> usize {
        self.index
            .iter()
            .map(|node| node.value().lock().len())
            .sum()
    }
    pub fn capacity(&self) -> usize {
        self.index
            .iter()
            .map(|entry| {
                let guard = entry.value().lock();
                guard.capacity()
            })
            .sum()
    }
    pub fn node_count(&self) -> usize {
        self.index.len()
    }
}

impl<T> FromIterator<T> for BTreeSet<T>
where
    T: Debug + Ord + Clone + Send,
{
    fn from_iter<K: IntoIterator<Item = T>>(iter: K) -> Self {
        let btree = BTreeSet::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

impl<T, const N: usize> From<[T; N]> for BTreeSet<T>
where
    T: Debug + Ord + Clone + Send,
{
    fn from(value: [T; N]) -> Self {
        let btree: BTreeSet<T> = Default::default();

        value.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

pub struct Iter<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    tree: &'a BTreeSet<T, Node>,
    current_front_node: Option<Arc<Mutex<Node>>>,
    current_front_node_guard: Option<ArcMutexGuard<RawMutex, Node>>,
    current_front_node_iter: Option<std::slice::Iter<'a, T>>,
    current_back_node: Option<Arc<Mutex<Node>>>,
    current_back_node_guard: Option<ArcMutexGuard<RawMutex, Node>>,
    current_back_node_iter: Option<std::slice::Iter<'a, T>>,
    current_front_value: Option<T>,
    current_back_value: Option<T>,
    met: bool,
}

impl<'a, T, Node> Iter<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    pub fn new(btree: &'a BTreeSet<T, Node>) -> Self {
        let current_front_node = btree.index.front().map(|e| e.value().clone());
        let current_back_node = btree.index.back().map(|e| e.value().clone());
        Self {
            tree: btree,
            current_front_node,
            current_front_node_guard: None,
            current_front_node_iter: None,
            current_back_node,
            current_back_node_guard: None,
            current_back_node_iter: None,
            current_front_value: None,
            current_back_value: None,
            met: false,
        }
    }
}

impl<'a, T, Node> Iterator for Iter<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.met {
                return None;
            }

            if self.current_front_node.is_none() {
                match self.tree.index.front() {
                    Some(e) => {
                        self.current_front_node = Some(e.value().clone());

                        if let Some(back_entry) = self.current_back_node.as_ref() {
                            if Arc::ptr_eq(e.value(), back_entry) {
                                self.current_front_node_guard = self.current_back_node_guard.take();
                                self.current_front_node_iter = self.current_back_node_iter.take();
                            }
                            continue;
                        }

                        self.current_front_node_guard = Some(
                            self.current_front_node
                                .as_ref()
                                .expect("was just set before")
                                .lock_arc(),
                        );
                        self.current_front_node_iter = Some(unsafe {
                            std::mem::transmute(
                                self.current_front_node_guard
                                    .as_ref()
                                    .expect("was just set before")
                                    .iter(),
                            )
                        });
                    }
                    None => {
                        return None;
                    }
                }
            }

            if self.current_back_node_guard.is_some() {
                self.current_back_node_guard = None;
                self.current_back_node_iter = None;
            }

            if let Some(iter) = self.current_front_node_iter.as_mut() {
                if let Some(value) = iter.next() {
                    if let Some(current_back_value) = self.current_back_value.as_ref() {
                        if value.ge(current_back_value) {
                            self.met = true;
                            return None;
                        }
                    }
                    self.current_front_value = Some(value.clone());
                    return Some(value);
                } else {
                    self.current_front_node_iter = None;
                    self.current_front_node_guard = None;

                    if let Some(current_node_entry) = self.tree.index.iter().find(|e| {
                        Arc::ptr_eq(
                            e.value(),
                            self.current_front_node
                                .as_ref()
                                .expect("was just set before"),
                        )
                    }) {
                        if let Some(next_node_entry) = current_node_entry.next() {
                            self.current_front_node = Some(next_node_entry.value().clone());

                            if let Some(back_entry) = self.current_back_node.as_ref() {
                                if Arc::ptr_eq(next_node_entry.value(), back_entry) {
                                    self.current_front_node_guard =
                                        self.current_back_node_guard.take();
                                    self.current_front_node_iter =
                                        self.current_back_node_iter.take();
                                }
                                continue;
                            }

                            self.current_front_node_guard = Some(
                                self.current_front_node
                                    .as_ref()
                                    .expect("was just set before")
                                    .lock_arc(),
                            );
                            self.current_front_node_iter = Some(unsafe {
                                std::mem::transmute(
                                    self.current_front_node_guard
                                        .as_ref()
                                        .expect("was just set before")
                                        .iter(),
                                )
                            });
                            continue;
                        } else {
                            self.current_front_node = None;
                            self.current_front_node_guard = None;
                            self.current_front_node_iter = None;
                            return None;
                        }
                    } else {
                        self.current_front_node = None;
                        self.current_front_node_guard = None;
                        self.current_front_node_iter = None;
                        return None;
                    }
                }
            } else {
                self.current_front_node_guard = Some(
                    self.current_front_node
                        .as_ref()
                        .expect("was just set before")
                        .lock_arc(),
                );
                self.current_front_node_iter = Some(unsafe {
                    std::mem::transmute(
                        self.current_front_node_guard
                            .as_ref()
                            .expect("was just set before")
                            .iter(),
                    )
                });

                if let Some(current_front_value) = self.current_front_value.as_ref() {
                    let g = self
                        .current_front_node_guard
                        .as_mut()
                        .expect("was just set before");
                    if let Some(rank) = g.rank(Bound::Excluded(current_front_value), true) {
                        let i = self
                            .current_front_node_iter
                            .as_mut()
                            .expect("was just set before");
                        if let Some(v) = i.nth(rank + 1) {
                            if let Some(current_back_value) = self.current_back_value.as_ref() {
                                if v.ge(current_back_value) {
                                    self.met = true;
                                    return None;
                                }
                            }
                            self.current_front_value = Some(v.clone());
                            return Some(v);
                        }
                    }
                    // else iter is exhausted, will continue in next loop iteration.
                    continue;
                }
            }
        }
    }
}

impl<'a, T, Node> DoubleEndedIterator for Iter<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if self.met {
                return None;
            }

            if self.current_back_node.is_none() {
                match self.tree.index.back() {
                    Some(e) => {
                        self.current_back_node = Some(e.value().clone());

                        if let Some(front_entry) = self.current_front_node.as_ref() {
                            if Arc::ptr_eq(e.value(), front_entry) {
                                self.current_back_node_guard = self.current_front_node_guard.take();
                                self.current_back_node_iter = self.current_front_node_iter.take();
                            }
                            continue;
                        }

                        self.current_back_node_guard = Some(
                            self.current_back_node
                                .as_ref()
                                .expect("was just set before")
                                .lock_arc(),
                        );
                        self.current_back_node_iter = Some(unsafe {
                            std::mem::transmute(
                                self.current_back_node_guard
                                    .as_ref()
                                    .expect("was just set before")
                                    .iter(),
                            )
                        });
                    }
                    None => {
                        return None;
                    }
                }
            }

            if self.current_front_node_guard.is_some() {
                self.current_front_node_guard = None;
                self.current_front_node_iter = None;
            }

            if let Some(iter) = self.current_back_node_iter.as_mut() {
                if let Some(value) = iter.next_back() {
                    if let Some(current_front_value) = self.current_front_value.as_ref() {
                        if value.le(current_front_value) {
                            self.met = true;
                            return None;
                        }
                    }
                    self.current_back_value = Some(value.clone());
                    return Some(value);
                } else {
                    self.current_back_node_iter = None;
                    self.current_back_node_guard = None;

                    if let Some(current_node_entry) = self.tree.index.iter().find(|e| {
                        Arc::ptr_eq(
                            e.value(),
                            self.current_back_node
                                .as_ref()
                                .expect("was just set before"),
                        )
                    }) {
                        if let Some(prev_node_entry) = current_node_entry.prev() {
                            self.current_back_node = Some(prev_node_entry.value().clone());

                            if let Some(front_entry) = self.current_front_node.as_ref() {
                                if Arc::ptr_eq(prev_node_entry.value(), front_entry) {
                                    self.current_back_node_guard =
                                        self.current_front_node_guard.take();
                                    self.current_back_node_iter =
                                        self.current_front_node_iter.take();
                                }
                                continue;
                            }

                            self.current_back_node_guard = Some(
                                self.current_back_node
                                    .as_ref()
                                    .expect("was just set before")
                                    .lock_arc(),
                            );
                            self.current_back_node_iter = Some(unsafe {
                                std::mem::transmute(
                                    self.current_back_node_guard
                                        .as_ref()
                                        .expect("was just set before")
                                        .iter(),
                                )
                            });
                            continue;
                        } else {
                            self.current_back_node = None;
                            self.current_back_node_guard = None;
                            self.current_back_node_iter = None;
                            return None;
                        }
                    } else {
                        self.current_back_node = None;
                        self.current_back_node_guard = None;
                        self.current_back_node_iter = None;
                        return None;
                    }
                }
            } else {
                self.current_back_node_guard = Some(
                    self.current_back_node
                        .as_ref()
                        .expect("was just set before")
                        .lock_arc(),
                );
                self.current_back_node_iter = Some(unsafe {
                    std::mem::transmute(
                        self.current_back_node_guard
                            .as_ref()
                            .expect("was just set before")
                            .iter(),
                    )
                });

                if let Some(current_back_value) = self.current_back_value.as_ref() {
                    let g = self
                        .current_back_node_guard
                        .as_mut()
                        .expect("was just set before");
                    if let Some(rank) = g.rank(Bound::Excluded(current_back_value), false) {
                        let i = self
                            .current_back_node_iter
                            .as_mut()
                            .expect("was just set before");
                        if let Some(v) = i.nth_back(rank + 1) {
                            if let Some(current_front_value) = self.current_front_value.as_ref() {
                                if v.le(current_front_value) {
                                    self.met = true;
                                    return None;
                                }
                            }
                            self.current_back_value = Some(v.clone());
                            return Some(v);
                        }
                    }
                    // else iter is exhausted, will continue in next loop iteration.
                    continue;
                }
            }
        }
    }
}

impl<'a, T: Debug + Ord + Clone + Send, Node: NodeLike<T> + Send + 'static> FusedIterator
    for Iter<'a, T, Node>
{
}

impl<'a, T, Node> IntoIterator for &'a BTreeSet<T, Node>
where
    T: Debug + Ord + Send + Clone,
    Node: NodeLike<T> + Send + 'static,
{
    type Item = &'a T;

    type IntoIter = Iter<'a, T, Node>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

pub struct Range<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    iter: Iter<'a, T, Node>,
}

impl<'a, T, Node> Range<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    pub fn new<Q, R>(btree: &'a BTreeSet<T, Node>, range: R) -> Self
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let _global_guard = btree.index_lock.read();

        let mut met = false;

        let start_bound = range.start_bound();
        let current_front_entry = btree.index.lower_bound(start_bound);

        let front_value = if let Some(front_entry) = current_front_entry.as_ref() {
            let front_guard = front_entry.value().lock_arc();
            if let Some(rank) = match start_bound {
                Bound::Included(v) => front_guard.rank(Bound::Included(v), true),
                Bound::Excluded(v) => front_guard.rank(Bound::Excluded(v), true),
                Bound::Unbounded => None,
            } {
                let mut front_iter = front_guard.iter();
                let front_value = front_iter.nth(rank).cloned();
                drop(front_guard);

                front_value
            } else {
                if let Some(pre_front_entry) = front_entry.prev() {
                    let pre_front_guard = pre_front_entry.value().lock_arc();
                    let front_value = pre_front_guard.iter().last().cloned();
                    drop(pre_front_guard);

                    front_value
                } else {
                    None
                }
            }
        } else {
            None
        };

        let end_bound = range.end_bound();
        let current_back_entry = btree
            .index
            .upper_bound(end_bound)
            .and_then(|e| e.next().or_else(|| btree.index.back()))
            .or_else(|| btree.index.front());

        let back_value = if let Some(back_entry) = current_back_entry.as_ref() {
            let back_guard = back_entry.value().lock_arc();
            if let Some(rank) = match end_bound {
                Bound::Included(v) => back_guard.rank(Bound::Included(v), false),
                Bound::Excluded(v) => back_guard.rank(Bound::Excluded(v), false),
                Bound::Unbounded => None,
            } {
                let mut back_iter = back_guard.iter();
                let back_value = back_iter.nth_back(rank).cloned();
                drop(back_guard);

                back_value
            } else {
                if let Some(prev_back_entry) = back_entry.next() {
                    let prev_back_guard = prev_back_entry.value().lock_arc();
                    let back_value = prev_back_guard.iter().next().cloned();
                    drop(prev_back_guard);

                    back_value
                } else {
                    None
                }
            }
        } else {
            None
        };

        if front_value.is_none() && back_value.is_none() {
            // in this case we iter full or no iter at all
            if start_bound != Bound::Unbounded || end_bound != Bound::Unbounded {
                if let Some(max) = btree
                    .index
                    .back()
                    .and_then(|e| e.value().lock_arc().max().cloned())
                {
                    if let Bound::Included(v) = start_bound {
                        if v > max.borrow() {
                            met = true;
                        }
                    } else if let Bound::Excluded(v) = start_bound {
                        if v >= max.borrow() {
                            met = true;
                        }
                    }
                }

                if let Some(min) = btree
                    .index
                    .front()
                    .and_then(|e| e.value().lock_arc().min().cloned())
                {
                    if let Bound::Included(v) = end_bound {
                        if v < min.borrow() {
                            met = true;
                        }
                    } else if let Bound::Excluded(v) = end_bound {
                        if v <= min.borrow() {
                            met = true;
                        }
                    }
                }
            }
        }

        Self {
            iter: Iter {
                tree: btree,
                current_front_node: current_front_entry.map(|e| e.value().clone()),
                current_front_node_guard: None,
                current_front_node_iter: None,
                current_back_node: current_back_entry.map(|e| e.value().clone()),
                current_back_node_guard: None,
                current_back_node_iter: None,
                current_front_value: front_value,
                current_back_value: back_value,
                met,
            },
        }
    }
}

impl<'a, T, Node> Iterator for Range<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T, Node> DoubleEndedIterator for Range<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<'a, T, Node> FusedIterator for Range<'a, T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
}

impl<'a, T, Node> BTreeSet<T, Node>
where
    T: Debug + Ord + Clone + Send + 'static,
    Node: NodeLike<T> + Send + 'static,
{
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
    pub fn iter(&'a self) -> Iter<'a, T, Node> {
        Iter::new(self)
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
    /// let mut set = BTreeSet::<usize>::new();
    /// set.insert(3);
    /// set.insert(5);
    /// set.insert(8);
    /// for &elem in set.range((Included(&4), Included(&8))) {
    ///     println!("{elem}");
    /// }
    /// assert_eq!(Some(&5), set.range(4..).next());
    /// ```
    pub fn range<Q, R>(&'a self, range: R) -> Range<'a, T, Node>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        Range::new(self, range)
    }
}

impl<T> BTreeSet<T>
where
    T: Debug + Ord + Clone + Send + 'static,
{
    pub fn remove_range<R, Q>(&self, range: R)
    where
        Q: Ord + ?Sized,
        T: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        let _global_guard = self.index_lock.write();

        let start_bound = range.start_bound();
        let end_bound = range.end_bound();
        let potential_front_entry = self.index.lower_bound(start_bound);
        let potential_back_entry = self.index.lower_bound(end_bound);

        let (potential_front_entry_guard, potential_front_position) =
            if let Some(front_entry) = potential_front_entry.clone() {
                let mut front_position = 0;

                let guard = front_entry.value().lock_arc();
                if let Some(position) = guard.rank(start_bound, true) {
                    front_position = position.wrapping_add(1);
                }

                (Some(guard), front_position)
            } else {
                (None, 0)
            };

        let (potential_back_entry_guard, potential_back_position) =
            if let Some(back_entry) = potential_back_entry.clone() {
                let mut back_position = 0;
                let mut guard = None;

                if let Some(front_entry) = potential_front_entry.as_ref() {
                    if !Arc::ptr_eq(back_entry.value(), front_entry.value()) {
                        let new_guard = back_entry.value().lock_arc();
                        let position = new_guard.rank(end_bound, true);
                        if let Some(position) = position {
                            back_position = position;
                        } else {
                            back_position = new_guard.len()
                        }

                        guard = Some(new_guard);
                    } else {
                        if let Some((len, position)) = potential_front_entry_guard
                            .as_ref()
                            .and_then(|g| Some((g.len(), g.rank(end_bound, true))))
                        {
                            if let Some(position) = position {
                                back_position = position;
                            } else {
                                back_position = len;
                            }
                        }
                    }
                }

                (guard, back_position)
            } else {
                (None, 0)
            };

        // If there is a front entry
        if let Some(mut front_entry_guard) = potential_front_entry_guard {
            let front_entry = potential_front_entry.unwrap();
            // But no back entry
            if let None = potential_back_entry_guard {
                // Then we drain the front entry
                let adjusted_back_position = {
                    if potential_front_position > potential_back_position {
                        front_entry_guard.len()
                    } else {
                        potential_back_position
                    }
                };
                front_entry_guard.drain(potential_front_position..adjusted_back_position);
                // Clone the mutex
                let old_entry_value = front_entry.value().clone();
                // Remove the entry
                front_entry.remove();
                // If it is empty, that's it
                if front_entry_guard.is_empty() {
                    return;
                }
                // Otherwise we insert it again with a new max
                let new_max = front_entry_guard.last().unwrap().clone();
                self.index.insert(new_max, old_entry_value);

                return;
            } else if let Some(mut back_entry_guard) = potential_back_entry_guard {
                let back_entry = potential_back_entry.unwrap();
                // Otherwise we remove every single node between them
                loop {
                    if let Some(next_entry) = front_entry.next() {
                        if next_entry.key().eq(back_entry.key()) {
                            break;
                        }

                        next_entry.remove();
                    } else {
                        break;
                    }
                }

                // And then trim the front from the left
                front_entry.remove();
                front_entry_guard.drain(potential_front_position..);
                if !front_entry_guard.is_empty() {
                    let new_front_max = front_entry_guard.last().unwrap().clone();
                    self.index
                        .insert(new_front_max, front_entry.value().clone());
                }

                // The back from the right
                back_entry.remove();
                back_entry_guard.drain(..potential_back_position);
                if !back_entry_guard.is_empty() {
                    let new_back_max = back_entry_guard.last().unwrap().clone();
                    self.index.insert(new_back_max, back_entry.value().clone());
                }

                // And that's it
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::concurrent::set::{BTreeSet, DEFAULT_INNER_SIZE};
    use rand::Rng;
    use std::collections::HashSet;
    use std::ops::Bound::Included;
    use std::sync::{Arc, Mutex};
    use std::thread;

    #[test]
    fn test_concurrent_insert() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let num_threads = 128;
        let operations_per_thread = 10000;
        let mut handles = vec![];

        let test_data: Vec<Vec<(i32, i32)>> = (0..num_threads)
            .map(|_| {
                let mut rng = rand::rng();
                (0..operations_per_thread)
                    .map(|_| {
                        let value = rng.random_range(0..100000);
                        let operation = rng.random_range(0..2);
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
                        let _a = set_clone.insert(value);
                        expected_values.lock().unwrap().insert(value);
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let expected_values = expected_values.lock().unwrap();
        assert_eq!(set.len(), expected_values.len());

        for value in expected_values.iter() {
            assert!(set.contains(value));
        }
    }

    #[test]
    fn test_insert_desc() {
        let set = Arc::new(BTreeSet::<i32>::new());

        assert!(set.insert(2));
        assert!(set.insert(1));
    }

    #[test]
    fn test_insert_st() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let mut rng = rand::rng();

        let n = 2048 * 100;
        let range = 0..n;
        let mut inserted_values = HashSet::new();
        for _ in range {
            let value = rng.random_range(0..n);
            if inserted_values.insert(value) {
                set.insert(value);
            }
        }

        assert_eq!(
            set.len(),
            inserted_values.len(),
            "Length did not match, missing: {:?}",
            set.index
                .iter()
                .flat_map(|entry| entry.value().lock().iter().cloned().collect::<Vec<_>>())
                .collect::<HashSet<_>>()
                .symmetric_difference(&inserted_values)
                .collect::<Vec<_>>()
        );
        for i in inserted_values {
            assert!(
                set.contains(&i),
                "Did not find: {} with index: {:?}",
                i,
                set.index.iter().collect::<Vec<_>>(),
            );
        }
    }

    #[test]
    fn test_single_element() {
        let set = BTreeSet::<i32>::new();
        set.insert(1);
        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_multiple_elements() {
        let set = BTreeSet::<i32>::new();
        set.insert(1);
        set.insert(2);
        set.insert(3);
        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_bidirectional_iteration() {
        let set = BTreeSet::<i32>::with_maximum_node_size(3);
        for i in 1..=20 {
            set.insert(i);
        }
        let mut iter = set.into_iter();
        for i in 0..10 {
            // (1, 20), (2, 19), (3, 18), (4, 17), (5, 16), (6, 15), (7, 14), (8, 13), (9, 12), (10, 11)
            let tree = set.index.iter().collect::<Vec<_>>();

            let expected_next = i + 1;
            let actual_next = iter.next();
            assert_eq!(actual_next, Some(&expected_next), "Tree: {:?}", tree);

            let expected_next_back = 20 - i;
            let actual_next_back = iter.next_back();
            assert_eq!(
                actual_next_back,
                Some(&expected_next_back),
                "Tree: {:?}",
                tree
            );
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_fused_iterator() {
        let set = BTreeSet::<i32>::new();
        set.insert(1);
        let mut iter = set.into_iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_fused_iterator_back() {
        let set = BTreeSet::<i32>::new();
        set.insert(1);
        let mut iter = set.into_iter();
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_out_of_bounds_range() {
        let btree: BTreeSet<usize> = BTreeSet::from_iter(0..10);
        assert_eq!(btree.range((Included(5), Included(10))).count(), 5);
        assert_eq!(btree.range((Included(5), Included(11))).count(), 5);
        assert_eq!(
            btree
                .range((Included(5), Included(10 + DEFAULT_INNER_SIZE)))
                .count(),
            5
        );
        assert_eq!(btree.range((Included(0), Included(11))).count(), 10);
    }

    #[test]
    fn test_iterating_over_blocks() {
        let btree = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE + 10)).into_iter());
        assert_eq!(btree.iter().count(), (0..(DEFAULT_INNER_SIZE + 10)).count());
        let start = btree
            .range(0..DEFAULT_INNER_SIZE)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();

        assert_eq!(start, (0..DEFAULT_INNER_SIZE).collect::<Vec<_>>());
        assert_eq!(
            btree
                .range(0..=DEFAULT_INNER_SIZE)
                .into_iter()
                .cloned()
                .collect::<Vec<_>>(),
            (0..=DEFAULT_INNER_SIZE).collect::<Vec<_>>()
        );
        assert_eq!(
            btree.range(0..=DEFAULT_INNER_SIZE + 1).count(),
            (0..=DEFAULT_INNER_SIZE + 1).count()
        );
        assert_eq!(
            btree.iter().rev().count(),
            (0..(DEFAULT_INNER_SIZE + 10)).count()
        );
        assert_eq!(
            btree.range(0..DEFAULT_INNER_SIZE).rev().count(),
            (0..DEFAULT_INNER_SIZE).count()
        );
        assert_eq!(
            btree.range(0..=DEFAULT_INNER_SIZE).rev().count(),
            (0..=DEFAULT_INNER_SIZE).count()
        );
        assert_eq!(
            btree.range(0..=DEFAULT_INNER_SIZE + 1).rev().count(),
            (0..=DEFAULT_INNER_SIZE + 1).count()
        );
    }

    #[test]
    fn test_empty_set() {
        let btree: BTreeSet<usize> = BTreeSet::new();
        assert_eq!(btree.iter().count(), 0);
        assert_eq!(btree.range(0..0).count(), 0);
        assert_eq!(btree.range(0..).count(), 0);
        assert_eq!(btree.range(..0).count(), 0);
        assert_eq!(btree.range(..).count(), 0);
        assert_eq!(btree.range(0..=0).count(), 0);
        assert_eq!(btree.range(..1).count(), 0);

        assert_eq!(btree.iter().rev().count(), 0);
        assert_eq!(btree.range(0..0).rev().count(), 0);
        assert_eq!(btree.range(..).rev().count(), 0);
        assert_eq!(btree.range(..1).rev().count(), 0);

        assert_eq!(btree.range(..DEFAULT_INNER_SIZE).count(), 0);
        assert_eq!(
            btree
                .range(DEFAULT_INNER_SIZE..DEFAULT_INNER_SIZE * 2)
                .count(),
            0
        );
    }

    #[test]
    fn test_remove_range() {
        // We have DEFAULT_INNER_SIZE * 2 elements
        let btree = BTreeSet::from_iter(0..(DEFAULT_INNER_SIZE * 2));
        let expected_len = DEFAULT_INNER_SIZE * 2;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // We remove 10 elements from the beginning, 5 included up to 15 excluded.
        btree.remove_range(5..15);
        let expected_len = expected_len - 10;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // Then take more 10 from the middle
        btree.remove_range(DEFAULT_INNER_SIZE - 5..DEFAULT_INNER_SIZE + 5);
        let expected_len = expected_len - 10;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // And then remove 512
        btree.remove_range(..DEFAULT_INNER_SIZE / 2);
        // We add +10 here because we are removing everything up to 512, but we already removed 5..15.
        let expected_len = expected_len - (DEFAULT_INNER_SIZE / 2) + 10;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // And then more (512 * 3) / 2
        let from = (DEFAULT_INNER_SIZE * 3) / 2;
        btree.remove_range(from..);
        let expected_len = expected_len - (DEFAULT_INNER_SIZE) - 5 + 10;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // We now clear the tree
        btree.remove_range(..);
        assert_eq!(btree.len(), 0);

        // Re-insert everything
        for i in 0..(DEFAULT_INNER_SIZE * 2) {
            btree.insert(i);
        }
        let expected_len = DEFAULT_INNER_SIZE * 2;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        btree.remove_range((std::ops::Bound::Excluded(5), std::ops::Bound::Excluded(15)));
        let expected_len = expected_len - 9;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        btree.remove_range((
            std::ops::Bound::Included(DEFAULT_INNER_SIZE),
            std::ops::Bound::Excluded(DEFAULT_INNER_SIZE + 10),
        ));
        let expected_len = expected_len - 10;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // This range exceeds the size of the tree
        btree.remove_range(DEFAULT_INNER_SIZE * 3..DEFAULT_INNER_SIZE * 4);
        let expected_len = expected_len;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);

        // This range starts at the very end of the tree, and exceeds it
        btree.remove_range(DEFAULT_INNER_SIZE * 2 - 5..DEFAULT_INNER_SIZE * 3);
        let expected_len = expected_len - 5;
        let actual_len = btree.len();
        assert_eq!(expected_len, actual_len);
    }

    #[test]
    fn test_remove_single_element() {
        let set = BTreeSet::<i32>::new();
        set.insert(5);
        assert!(set.contains(&5));
        assert!(set.remove(&5).is_some());
        assert!(!set.contains(&5));
        assert!(!set.remove(&5).is_some());
    }

    #[test]
    fn test_remove_multiple_elements() {
        let set = BTreeSet::<i32>::new();
        for i in 0..2048 {
            set.insert(i);
        }
        for i in 0..2048 {
            assert!(set.remove(&i).is_some());
            assert!(!set.contains(&i));
        }
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_remove_non_existent() {
        let set = BTreeSet::<i32>::new();
        set.insert(5);
        assert!(!set.remove(&10).is_some());
        assert!(set.contains(&5));
    }

    #[test]
    fn test_remove_stress() {
        let set = Arc::new(BTreeSet::<i32>::new());
        const NUM_ELEMENTS: i32 = 10000;

        for i in 0..NUM_ELEMENTS {
            set.insert(i);
        }
        assert_eq!(
            set.len(),
            NUM_ELEMENTS as usize,
            "Incorrect size after insertion"
        );

        let num_threads = 8;
        let elements_per_thread = NUM_ELEMENTS / num_threads;
        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    for i in (t * elements_per_thread)..((t + 1) * elements_per_thread) {
                        if i % 2 == 1 {
                            assert!(set.remove(&i).is_some(), "Failed to remove {}", i);
                        }
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(
            set.len(),
            NUM_ELEMENTS as usize / 2,
            "Incorrect size after removal"
        );

        for i in 0..NUM_ELEMENTS {
            if i % 2 == 0 {
                assert!(set.contains(&i), "Even number {} should be in the set", i);
            } else {
                assert!(
                    !set.contains(&i),
                    "Odd number {} should not be in the set",
                    i
                );
            }
        }
    }

    #[test]
    fn test_remove_all_elements() {
        let set = BTreeSet::<i32>::new();
        let n = 2048;

        for i in 0..n {
            set.insert(i);
        }

        for i in 0..n {
            assert!(set.remove(&i).is_some(), "Failed to remove {}", i);
        }

        assert_eq!(set.len(), 0, "Set should be empty");

        for i in 0..n {
            assert!(!set.contains(&i), "Element {} should not be in the set", i);
        }
    }

    #[test]
    fn test_range_edge_cases() {
        let set = BTreeSet::<i32>::with_maximum_node_size(10);
        for i in 0..20 {
            set.insert(i);
        }
        // Nodes are:
        // [0, 1, 2, 3, 4]
        // [5, 6, 7, 8, 9]
        // [10, 11, 12, 13, 14, 15, 16, 17, 18, 19]

        // First value of the node only
        assert_eq!(set.range(0..=0).collect::<Vec<_>>(), vec![&0]);
        assert_eq!(set.range(0..1).collect::<Vec<_>>(), vec![&0]);

        assert_eq!(set.range(5..=5).collect::<Vec<_>>(), vec![&5]);
        assert_eq!(set.range(5..6).collect::<Vec<_>>(), vec![&5]);

        assert_eq!(set.range(10..=10).collect::<Vec<_>>(), vec![&10]);
        assert_eq!(set.range(10..11).collect::<Vec<_>>(), vec![&10]);

        // From first value to middle
        assert_eq!(set.range(0..=3).collect::<Vec<_>>(), vec![&0, &1, &2, &3]);
        assert_eq!(set.range(0..3).collect::<Vec<_>>(), vec![&0, &1, &2]);

        assert_eq!(set.range(5..=8).collect::<Vec<_>>(), vec![&5, &6, &7, &8]);
        assert_eq!(set.range(5..8).collect::<Vec<_>>(), vec![&5, &6, &7]);

        assert_eq!(
            set.range(10..=13).collect::<Vec<_>>(),
            vec![&10, &11, &12, &13]
        );
        assert_eq!(set.range(10..13).collect::<Vec<_>>(), vec![&10, &11, &12]);

        // Last value of the node
        assert_eq!(set.range(4..=4).collect::<Vec<_>>(), vec![&4]);
        assert_eq!(set.range(4..5).collect::<Vec<_>>(), vec![&4]);

        assert_eq!(set.range(9..=9).collect::<Vec<_>>(), vec![&9]);
        assert_eq!(set.range(9..10).collect::<Vec<_>>(), vec![&9]);

        assert_eq!(set.range(19..=19).collect::<Vec<_>>(), vec![&19]);
        assert_eq!(set.range(19..20).collect::<Vec<_>>(), vec![&19]);

        // From middle to last value of the node
        assert_eq!(set.range(17..=19).collect::<Vec<_>>(), vec![&17, &18, &19]);
        assert_eq!(set.range(17..20).collect::<Vec<_>>(), vec![&17, &18, &19]);

        assert_eq!(set.range(7..=9).collect::<Vec<_>>(), vec![&7, &8, &9]);
        assert_eq!(set.range(7..10).collect::<Vec<_>>(), vec![&7, &8, &9]);

        assert_eq!(set.range(2..=4).collect::<Vec<_>>(), vec![&2, &3, &4]);
        assert_eq!(set.range(2..5).collect::<Vec<_>>(), vec![&2, &3, &4]);

        // Full node
        assert_eq!(
            set.range(0..=4).collect::<Vec<_>>(),
            vec![&0, &1, &2, &3, &4]
        );
        assert_eq!(
            set.range(0..5).collect::<Vec<_>>(),
            vec![&0, &1, &2, &3, &4]
        );

        assert_eq!(
            set.range(5..=9).collect::<Vec<_>>(),
            vec![&5, &6, &7, &8, &9]
        );
        assert_eq!(
            set.range(5..10).collect::<Vec<_>>(),
            vec![&5, &6, &7, &8, &9]
        );

        assert_eq!(
            set.range(10..=19).collect::<Vec<_>>(),
            vec![&10, &11, &12, &13, &14, &15, &16, &17, &18, &19]
        );
        assert_eq!(
            set.range(10..20).collect::<Vec<_>>(),
            vec![&10, &11, &12, &13, &14, &15, &16, &17, &18, &19]
        );

        // Node intersection
        assert_eq!(set.range(3..=6).collect::<Vec<_>>(), vec![&3, &4, &5, &6]);
        assert_eq!(set.range(3..7).collect::<Vec<_>>(), vec![&3, &4, &5, &6]);

        assert_eq!(
            set.range(8..=11).collect::<Vec<_>>(),
            vec![&8, &9, &10, &11]
        );
        assert_eq!(set.range(8..12).collect::<Vec<_>>(), vec![&8, &9, &10, &11]);

        // REVERSED

        // First value of the node only
        assert_eq!(set.range(0..=0).rev().collect::<Vec<_>>(), vec![&0]);
        assert_eq!(set.range(0..1).rev().collect::<Vec<_>>(), vec![&0]);

        assert_eq!(set.range(5..=5).rev().collect::<Vec<_>>(), vec![&5]);
        assert_eq!(set.range(5..6).rev().collect::<Vec<_>>(), vec![&5]);

        assert_eq!(set.range(10..=10).rev().collect::<Vec<_>>(), vec![&10]);
        assert_eq!(set.range(10..11).rev().collect::<Vec<_>>(), vec![&10]);

        // From first value to middle
        assert_eq!(
            set.range(0..=3).rev().collect::<Vec<_>>(),
            vec![&3, &2, &1, &0]
        );
        assert_eq!(set.range(0..3).rev().collect::<Vec<_>>(), vec![&2, &1, &0]);

        assert_eq!(
            set.range(5..=8).rev().collect::<Vec<_>>(),
            vec![&8, &7, &6, &5]
        );
        assert_eq!(set.range(5..8).rev().collect::<Vec<_>>(), vec![&7, &6, &5]);

        assert_eq!(
            set.range(10..=13).rev().collect::<Vec<_>>(),
            vec![&13, &12, &11, &10]
        );
        assert_eq!(
            set.range(10..13).rev().collect::<Vec<_>>(),
            vec![&12, &11, &10]
        );

        // Last value of the node
        assert_eq!(set.range(4..=4).rev().collect::<Vec<_>>(), vec![&4]);
        assert_eq!(set.range(4..5).rev().collect::<Vec<_>>(), vec![&4]);

        assert_eq!(set.range(9..=9).rev().collect::<Vec<_>>(), vec![&9]);
        assert_eq!(set.range(9..10).rev().collect::<Vec<_>>(), vec![&9]);

        assert_eq!(set.range(19..=19).rev().collect::<Vec<_>>(), vec![&19]);
        assert_eq!(set.range(19..20).rev().collect::<Vec<_>>(), vec![&19]);

        // From middle to last value of the node
        assert_eq!(
            set.range(17..=19).rev().collect::<Vec<_>>(),
            vec![&19, &18, &17]
        );
        assert_eq!(
            set.range(17..20).rev().collect::<Vec<_>>(),
            vec![&19, &18, &17]
        );

        assert_eq!(set.range(7..=9).rev().collect::<Vec<_>>(), vec![&9, &8, &7]);
        assert_eq!(set.range(7..10).rev().collect::<Vec<_>>(), vec![&9, &8, &7]);

        assert_eq!(set.range(2..=4).rev().collect::<Vec<_>>(), vec![&4, &3, &2]);
        assert_eq!(set.range(2..5).rev().collect::<Vec<_>>(), vec![&4, &3, &2]);

        // Full node
        assert_eq!(
            set.range(0..=4).rev().collect::<Vec<_>>(),
            vec![&4, &3, &2, &1, &0]
        );
        assert_eq!(
            set.range(0..5).rev().collect::<Vec<_>>(),
            vec![&4, &3, &2, &1, &0]
        );

        assert_eq!(
            set.range(5..=9).rev().collect::<Vec<_>>(),
            vec![&9, &8, &7, &6, &5]
        );
        assert_eq!(
            set.range(5..10).rev().collect::<Vec<_>>(),
            vec![&9, &8, &7, &6, &5]
        );

        assert_eq!(
            set.range(10..=19).rev().collect::<Vec<_>>(),
            vec![&19, &18, &17, &16, &15, &14, &13, &12, &11, &10]
        );
        assert_eq!(
            set.range(10..20).rev().collect::<Vec<_>>(),
            vec![&19, &18, &17, &16, &15, &14, &13, &12, &11, &10]
        );

        // Node intersection
        assert_eq!(
            set.range(3..=6).rev().collect::<Vec<_>>(),
            vec![&6, &5, &4, &3]
        );
        assert_eq!(
            set.range(3..7).rev().collect::<Vec<_>>(),
            vec![&6, &5, &4, &3]
        );

        assert_eq!(
            set.range(8..=11).rev().collect::<Vec<_>>(),
            vec![&11, &10, &9, &8]
        );
        assert_eq!(
            set.range(8..12).rev().collect::<Vec<_>>(),
            vec![&11, &10, &9, &8]
        );

        // Non-existent range
        assert!(set.range(20..).collect::<Vec<_>>().is_empty());
        assert!(set.range(..0).collect::<Vec<_>>().is_empty());
        assert!(set.range(20..).rev().collect::<Vec<_>>().is_empty());
        assert!(set.range(..0).rev().collect::<Vec<_>>().is_empty());
    }

    #[test]
    fn parallel_iter_and_mut() {
        let set = Arc::new(BTreeSet::<i32>::new());
        for i in 0..10_000 {
            set.insert(i);
        }

        let set_clone = Arc::clone(&set);
        let _ = thread::spawn(move || {
            for _ in 0..1000 {
                let mut _sum = 0;
                for &value in set_clone.iter() {
                    _sum += value;
                }
            }
        });

        for i in 10_000..20_000 {
            set.insert(i);
        }
    }
}