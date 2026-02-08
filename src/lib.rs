#[cfg(feature = "concurrent")]
pub mod concurrent;

#[cfg(feature = "concurrent")]
pub mod cdc;

pub mod core;

use crate::Entry::{Occupied, Vacant};
use core::constants::DEFAULT_INNER_SIZE;
use core::node::*;
use core::pair::Pair;
use ftree::FenwickTree;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::Bound;
use std::iter::FusedIterator;
use std::mem::swap;
use std::ops::{Index, RangeBounds};

type Node<T> = Vec<T>;

/// An ordered set based on a B-Tree.
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
/// Iterators returned by [`BTreeSet::iter`] produce their items in order, and take worst-case
/// logarithmic and amortized constant time per item returned.
///
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
///
/// # Examples
///
/// ```
/// use indexset::BTreeSet;
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
/// use indexset::BTreeSet;
///
/// let set = BTreeSet::from_iter([1, 2, 3]);
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BTreeSet<T>
where
    T: Ord,
{
    inner: Vec<Node<T>>,
    index: FenwickTree<usize>,
    node_capacity: usize,
    len: usize,
}

impl<T: Ord> BTreeSet<T> {
    /// Makes a new, empty `BTreeSet` with maximum node size 1024. Allocates one vec of capacity 1024.
    ///
    /// Note that this does not mean that the maximum number of items is 1024.
    ///
    /// In case you would like to make a tree with a different maximum node size, use the
    /// `with_maximum_node_size` method.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// use indexset::BTreeSet;
    ///
    /// let mut set: BTreeSet<i32> = BTreeSet::new();
    /// ```
    pub fn new() -> Self {
        Self {
            ..Default::default()
        }
    }
    /// Makes a new, empty `BTreeSet` with the given maximum node size. Allocates one vec with
    /// the capacity set to be the specified node size.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// use indexset::BTreeSet;
    ///
    /// let mut set: BTreeSet<i32> = BTreeSet::with_maximum_node_size(128);
    pub fn with_maximum_node_size(maximum_node_size: usize) -> Self {
        let mut new: Self = Default::default();
        new.inner = vec![Node::with_capacity(maximum_node_size)];
        new.node_capacity = maximum_node_size;

        new
    }
    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// v.insert(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner = vec![Node::with_capacity(self.node_capacity)];
        self.index = FenwickTree::from_iter(vec![0]);
        self.len = 0;
    }
    fn locate_node<Q>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut node_idx = self.inner.partition_point(|node| {
            if let Some(&max) = node.last().as_ref() {
                return max.borrow() < value;
            };

            false
        });

        // When value is greater than all elements inside inner[node_idx], then len
        // of inner[node_idx], which is not a valid place for insertion, is returned. It will
        // never return less than 0, so it is only necessary to check whether it is out of bounds
        // from the right
        if self.inner.get(node_idx).is_none() {
            node_idx -= 1
        }

        node_idx
    }
    fn locate_node_cmp<P, Q>(&self, mut cmp: P) -> usize
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
    {
        let mut node_idx = self.inner.partition_point(|node| {
            if let Some(max) = node.last() {
                return cmp(max.borrow());
            }

            true
        });

        if self.inner.get(node_idx).is_none() {
            node_idx -= 1
        }

        node_idx
    }
    fn locate_value<Q>(&self, value: &Q) -> (usize, usize)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let node_idx = self.locate_node(value);
        let position_within_node =
            self.inner[node_idx].partition_point(|item| item.borrow() < value);

        (node_idx, position_within_node)
    }
    fn locate_value_cmp<P, Q>(&self, mut cmp: P) -> (usize, usize)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
    {
        let node_idx = self.locate_node_cmp(&mut cmp);
        let position_within_node = self.inner[node_idx].partition_point(|item| cmp(item.borrow()));

        (node_idx, position_within_node)
    }
    fn locate_ith(&self, idx: usize) -> (usize, usize) {
        let mut node_index = self.index.index_of(idx);
        let mut offset = 0;

        if node_index != 0 {
            offset = self.index.prefix_sum(node_index, 0);
        }

        let mut position_within_node = idx - offset;
        if let Some(node) = self.inner.get(node_index) {
            if position_within_node == node.len() {
                node_index += 1;
                position_within_node = 0;
            }
        }

        (node_index, position_within_node)
    }
    /// Returns a reference to the element in the i-th position of the set, if any.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([1, 2, 3]);
    /// assert_eq!(set.get_index(0), Some(&1));
    /// assert_eq!(set.get_index(2), Some(&3));
    /// assert_eq!(set.get_index(4), None);
    /// ```
    pub fn get_index(&self, idx: usize) -> Option<&T> {
        let (node_idx, position_within_node) = self.locate_ith(idx);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            return candidate_node.get(position_within_node);
        }

        None
    }
    fn get_mut_index(&mut self, index: usize) -> Option<&mut T> {
        let (node_idx, position_within_node) = self.locate_ith(index);
        if let Some(_) = self.inner.get(node_idx) {
            return self.inner[node_idx].get_mut(position_within_node);
        }

        None
    }
    /// Returns a reference to the element in the set, if any, that is equal to
    /// the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (node_idx, position_within_node) = self.locate_value(value);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            return candidate_node.get(position_within_node);
        }

        None
    }
    /// Returns a reference to the first element in the set, if any, that is not less than the
    /// input.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([1, 2, 3, 5]);
    /// assert_eq!(set.lower_bound(&2), Some(&2));
    /// assert_eq!(set.lower_bound(&4), Some(&5));
    /// ```
    pub fn lower_bound<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (node_idx, position_within_node) = self.locate_value(value);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            return candidate_node.get(position_within_node);
        }

        None
    }
    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
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
    /// See the [module-level documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        let node_idx = self.locate_node(&value);
        if self.inner[node_idx].len() == self.node_capacity {
            let new_node = self.inner[node_idx].halve();
            let mut insert_node_idx = node_idx;
            if value >= new_node[0] {
                insert_node_idx += 1;
            }

            self.inner.insert(node_idx + 1, new_node);
            if NodeLike::insert(&mut self.inner[insert_node_idx], value).0 {
                // Reconstruct the index after the new node and inner value inserts.
                self.index = FenwickTree::from_iter(self.inner.iter().map(|node| node.len()));
                self.len += 1;

                true
            } else {
                // Reconstruct the index after the new node insert even if the new value wasn't added.
                self.index = FenwickTree::from_iter(self.inner.iter().map(|node| node.len()));
                false
            }
        } else if NodeLike::insert(&mut self.inner[node_idx], value).0 {
            self.index.add_at(node_idx, 1);
            self.len += 1;

            true
        } else {
            false
        }
    }

    /// Adds a value to the set, replacing the existing element, if any, that is
    /// equal to the value. Returns the replaced element.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    /// set.insert(Vec::<i32>::new());
    ///
    /// assert_eq!(set.get(&[][..]).unwrap().capacity(), 0);
    /// println!("{}", set.replace(Vec::with_capacity(10)).unwrap().capacity());
    /// println!("{}", set.get(&[][..]).unwrap().capacity());
    /// assert_eq!(set.get(&[][..]).unwrap().capacity(), 10);
    /// ```
    pub fn replace(&mut self, value: T) -> Option<T> {
        let replaced_element = self.take(&value);
        self.insert(value);

        replaced_element
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
    /// use indexset::BTreeSet;
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
        let (node_idx, position_within_node) = self.locate_value(value);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            if let Some(candidate_value) = candidate_node.get(position_within_node) {
                return value == candidate_value.borrow();
            }
        }

        false
    }
    fn contains_cmp<P, Q, R>(&self, cmp: P, mut cmp2: R) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
        R: FnMut(&Q) -> bool,
    {
        let (node_idx, position_within_node) = self.locate_value_cmp(cmp);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            if let Some(candidate_value) = candidate_node.get(position_within_node) {
                return cmp2(candidate_value.borrow());
            }
        }

        false
    }
    fn delete_at(&mut self, node_idx: usize, position_within_node: usize) -> T {
        let removal = self.inner[node_idx].remove(position_within_node);

        let mut decrease_length = false;
        // check whether the node has to be deleted
        if self.inner[node_idx].len() == 0 {
            // delete it as long as it is not the last remaining node
            if self.inner.len() > 1 {
                self.inner.remove(node_idx);
                self.len -= 1;
                self.index = FenwickTree::from_iter(self.inner.iter().map(|node| node.len()));
            } else {
                decrease_length = true;
            }
        } else {
            decrease_length = true;
        }

        if decrease_length {
            self.index.sub_at(node_idx, 1);
            self.len -= 1;
        }

        removal
    }
    fn delete<Q>(&mut self, value: &Q) -> (Option<T>, bool)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut removed = false;
        let mut removal = None;
        let (node_idx, position_within_node) = self.locate_value(value);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            if let Some(candidate_value) = candidate_node.get(position_within_node) {
                if value == candidate_value.borrow() {
                    removal = Some(self.delete_at(node_idx, position_within_node));
                    removed = true;
                }
            }
        }

        (removal, removed)
    }
    fn delete_cmp<P, Q, R>(&mut self, cmp: P, mut cmp2: R) -> (Option<T>, bool)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
        R: FnMut(&Q) -> bool,
    {
        let mut removed = false;
        let mut removal = None;
        let (node_idx, position_within_node) = self.locate_value_cmp(cmp);
        if let Some(candidate_node) = self.inner.get(node_idx) {
            if let Some(candidate_value) = candidate_node.get(position_within_node) {
                if cmp2(candidate_value.borrow()) {
                    removal = Some(self.delete_at(node_idx, position_within_node));
                    removed = true;
                }
            }
        }

        (removal, removed)
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
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.delete(value).1
    }
    /// Removes and returns the element in the set, if any, that is equal to
    /// the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::from_iter([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.delete(value).0
    }
    /// Returns a reference to the first element in the set, if any.
    /// This element is always the minimum of all elements in the set.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    /// assert_eq!(set.first(), None);
    /// set.insert(1);
    /// assert_eq!(set.first(), Some(&1));
    /// set.insert(2);
    /// assert_eq!(set.first(), Some(&1));
    /// ```
    pub fn first(&self) -> Option<&T> {
        if let Some(candidate_node) = self.inner.get(0) {
            return candidate_node.get(0);
        }

        None
    }
    /// Returns a reference to the last element in the set, if any.
    /// This element is always the maximum of all elements in the set.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    /// assert_eq!(set.last(), None);
    /// set.insert(1);
    /// assert_eq!(set.last(), Some(&1));
    /// set.insert(2);
    /// assert_eq!(set.last(), Some(&2));
    /// ```
    pub fn last(&self) -> Option<&T> {
        if let Some(candidate_node) = self.inner.get(self.inner.len() - 1) {
            if candidate_node.len() > 0 {
                return candidate_node.get(candidate_node.len() - 1);
            }
        }

        None
    }
    /// Removes the first element from the set and returns it, if any.
    /// The first element is always the minimum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// set.insert(1);
    /// while let Some(n) = set.pop_first() {
    ///     assert_eq!(n, 1);
    /// }
    /// assert!(set.is_empty());
    /// ```
    pub fn pop_first(&mut self) -> Option<T> {
        let (first_node_idx, first_position_within_node) = (0, 0);
        if let Some(candidate_node) = self.inner.get(first_node_idx) {
            if candidate_node.get(first_position_within_node).is_some() {
                return Some(self.delete_at(first_node_idx, first_position_within_node));
            }
        }

        None
    }
    /// Removes the i-th element from the set and returns it, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// set.insert(1);
    /// set.insert(2);
    /// assert_eq!(set.pop_index(0), 1);
    /// assert_eq!(set.pop_index(0), 2);
    /// assert!(set.is_empty());
    /// ```
    pub fn pop_index(&mut self, idx: usize) -> T {
        let (node_idx, position_within_node) = self.locate_ith(idx);

        self.delete_at(node_idx, position_within_node)
    }
    /// Removes the last element from the set and returns it, if any.
    /// The last element is always the maximum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::new();
    ///
    /// set.insert(1);
    /// while let Some(n) = set.pop_last() {
    ///     assert_eq!(n, 1);
    /// }
    /// assert!(set.is_empty());
    /// ```
    pub fn pop_last(&mut self) -> Option<T> {
        let last_node_idx = self.inner.len() - 1;
        let mut last_position_within_node = self.inner[last_node_idx].len();
        last_position_within_node = last_position_within_node.saturating_sub(1);

        if let Some(candidate_node) = self.inner.get(last_node_idx) {
            if candidate_node.get(last_position_within_node).is_some() {
                return Some(self.delete_at(last_node_idx, last_position_within_node));
            }
        }

        None
    }
    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut v = BTreeSet::new();
    /// assert!(v.is_empty());
    /// v.insert(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Returns `true` if the set is a subset of another,
    /// i.e., `other` contains at least all the elements in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let sup = BTreeSet::from_iter([1, 2, 3]);
    /// let mut set = BTreeSet::new();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2);
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4);
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    pub fn is_subset(&self, other: &Self) -> bool {
        if self.difference(other).next().is_some() {
            return false;
        }

        true
    }
    /// Returns `true` if the set is a superset of another,
    /// i.e., `self` contains at least all the elements in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let sub = BTreeSet::from_iter([1, 2]);
    /// let mut set = BTreeSet::new();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2);
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    pub fn is_superset(&self, other: &Self) -> bool {
        if other.difference(self).next().is_some() {
            return false;
        }

        true
    }
    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let a = BTreeSet::from_iter([1, 2, 3]);
    /// let mut b = BTreeSet::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint(&self, other: &Self) -> bool {
        if self.intersection(other).next().is_some() {
            return false;
        }

        true
    }
    /// Gets an iterator that visits the elements in the `BTreeSet` in ascending
    /// order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
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
    /// use indexset::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([3, 1, 2]);
    /// let mut set_iter = set.iter();
    /// assert_eq!(set_iter.next(), Some(&1));
    /// assert_eq!(set_iter.next(), Some(&2));
    /// assert_eq!(set_iter.next(), Some(&3));
    /// assert_eq!(set_iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }
    /// Visits the elements representing the union,
    /// i.e., all the elements in `self` or `other`, without duplicates,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    ///
    /// let mut b = BTreeSet::new();
    /// b.insert(2);
    ///
    /// let union: Vec<_> = a.union(&b).cloned().collect();
    /// assert_eq!(union, [1, 2]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a Self) -> Union<'a, T> {
        Union {
            merge_iter: MergeIter {
                start: true,
                left_iter: self.iter(),
                current_left: None,
                right_iter: other.iter(),
                current_right: None,
            },
        }
    }
    /// Visits the elements representing the difference,
    /// i.e., the elements that are in `self` but not in `other`,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::new();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let diff: Vec<_> = a.difference(&b).cloned().collect();
    /// assert_eq!(diff, [1]);
    /// ```
    pub fn difference<'a>(&'a self, other: &'a Self) -> Difference<'a, T> {
        Difference {
            merge_iter: MergeIter {
                start: true,
                left_iter: self.iter(),
                current_left: None,
                right_iter: other.iter(),
                current_right: None,
            },
        }
    }
    /// Visits the elements representing the symmetric difference,
    /// i.e., the elements that are in `self` or in `other` but not in both,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::new();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let sym_diff: Vec<_> = a.symmetric_difference(&b).cloned().collect();
    /// assert_eq!(sym_diff, [1, 3]);
    /// ```
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> SymmetricDifference<'a, T> {
        SymmetricDifference {
            merge_iter: MergeIter {
                start: true,
                left_iter: self.iter(),
                current_left: None,
                right_iter: other.iter(),
                current_right: None,
            },
        }
    }
    /// Visits the elements representing the intersection,
    /// i.e., the elements that are both in `self` and `other`,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::new();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let intersection: Vec<_> = a.intersection(&b).cloned().collect();
    /// assert_eq!(intersection, [2]);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a Self) -> Intersection<'a, T> {
        Intersection {
            merge_iter: MergeIter {
                start: true,
                left_iter: self.iter(),
                current_left: None,
                right_iter: other.iter(),
                current_right: None,
            },
        }
    }
    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// The elements are visited in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut set = BTreeSet::from_iter([1, 2, 3, 4, 5, 6]);
    /// // Keep only the even numbers.
    /// set.retain(|&k| k % 2 == 0);
    /// assert!(set.iter().eq([2, 4, 6].iter()));
    /// ```
    pub fn retain<F, Q>(&mut self, mut f: F)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        F: FnMut(&Q) -> bool,
    {
        let mut positions_to_delete = vec![];
        for (node_idx, node) in self.inner.iter().enumerate() {
            for (position_within_node, item) in node.iter().enumerate() {
                if !f(item.borrow()) {
                    positions_to_delete.push((node_idx, position_within_node));
                }
            }
        }
        positions_to_delete.reverse();

        positions_to_delete
            .into_iter()
            .for_each(|(node_idx, position_within_node)| {
                self.delete_at(node_idx, position_within_node);
            })
    }
    fn split_off_cmp<P, Q>(&mut self, cmp: P) -> Self
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
    {
        let (node_idx, position_within_node) = self.locate_value_cmp(cmp);
        let first_node = self.inner[node_idx].split_off(position_within_node);
        let mut remaining_nodes = vec![];
        while self.inner.len() > node_idx + 1 {
            remaining_nodes.push(self.inner.pop().unwrap());
        }
        remaining_nodes.reverse();
        remaining_nodes.insert(0, first_node);
        let mut latter_half = BTreeSet::default();
        latter_half.len = remaining_nodes.iter().map(|node| node.len()).sum();
        latter_half.inner = remaining_nodes;
        latter_half.index = FenwickTree::from_iter(latter_half.inner.iter().map(|node| node.len()));

        if self.inner[node_idx].len() == 0 && self.inner.len() > 1 {
            self.inner.remove(node_idx);
        }

        self.index = FenwickTree::from_iter(self.inner.iter().map(|node| node.len()));
        self.len = self.inner.iter().map(|node| node.len()).sum();

        latter_half
    }
    /// Splits the collection into two at the value. Returns a new collection
    /// with all elements greater than or equal to the value.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    /// a.insert(2);
    /// a.insert(3);
    /// a.insert(17);
    /// a.insert(41);
    ///
    /// let b = a.split_off(&3);
    ///
    /// assert_eq!(a.len(), 2);
    /// assert_eq!(b.len(), 3);
    ///
    /// assert!(a.contains(&1));
    /// assert!(a.contains(&2));
    ///
    /// assert!(b.contains(&3));
    /// assert!(b.contains(&17));
    /// assert!(b.contains(&41));
    /// ```
    pub fn split_off<Q>(&mut self, value: &Q) -> Self
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let (node_idx, position_within_node) = self.locate_value(value);
        let first_node = self.inner[node_idx].split_off(position_within_node);
        let mut remaining_nodes = vec![];
        while self.inner.len() > node_idx + 1 {
            remaining_nodes.push(self.inner.pop().unwrap());
        }
        remaining_nodes.reverse();
        remaining_nodes.insert(0, first_node);
        let mut latter_half = BTreeSet::default();
        latter_half.len = remaining_nodes.iter().map(|node| node.len()).sum();
        latter_half.inner = remaining_nodes;
        latter_half.index = FenwickTree::from_iter(latter_half.inner.iter().map(|node| node.len()));

        if self.inner[node_idx].len() == 0 && self.inner.len() > 1 {
            self.inner.remove(node_idx);
        }

        self.index = FenwickTree::from_iter(self.inner.iter().map(|node| node.len()));
        self.len = self.inner.iter().map(|node| node.len()).sum();

        latter_half
    }
    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let mut a = BTreeSet::new();
    /// a.insert(1);
    /// a.insert(2);
    /// a.insert(3);
    ///
    /// let mut b = BTreeSet::new();
    /// b.insert(3);
    /// b.insert(4);
    /// b.insert(5);
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert!(a.contains(&1));
    /// assert!(a.contains(&2));
    /// assert!(a.contains(&3));
    /// assert!(a.contains(&4));
    /// assert!(a.contains(&5));
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        while let Some(value) = other.pop_first() {
            self.replace(value);
        }
    }
    fn resolve_range<R>(&self, range: R) -> ((usize, usize, usize), (usize, usize, usize))
    where
        R: RangeBounds<usize>,
    {
        let mut global_front_idx: usize = 0;
        let mut global_back_idx: usize =
            self.index.prefix_sum(self.inner.len(), 0).saturating_sub(1);

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
        // Figuring out nodes
        let (front_node_idx, front_start_idx) = self.locate_ith(global_front_idx);
        let (back_node_idx, back_start_idx) = self.locate_ith(global_back_idx);

        (
            (global_front_idx, front_node_idx, front_start_idx),
            (global_back_idx, back_node_idx, back_start_idx),
        )
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
    /// use indexset::BTreeSet;
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
        let start_idx = match range.start_bound() {
            Bound::Included(bound) => self.rank(bound),
            Bound::Excluded(bound) => self.rank(bound) + 1,
            Bound::Unbounded => 0,
        };
        let end_idx = match range.end_bound() {
            Bound::Included(bound) => self.rank(bound),
            Bound::Excluded(bound) => self.rank(bound).saturating_sub(1),
            Bound::Unbounded => self.len().saturating_sub(1),
        };

        self.range_idx(start_idx..=end_idx)
    }
    /// Returns the position in which the given element would fall in the already-existing sorted
    /// order.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeSet;
    ///
    /// let set = BTreeSet::from_iter([1, 2, 3]);
    /// assert_eq!(set.rank(&1), 0);
    /// assert_eq!(set.rank(&3), 2);
    /// assert_eq!(set.rank(&4), 3);
    /// assert_eq!(set.rank(&100), 3);
    /// ```
    pub fn rank<Q>(&self, value: &Q) -> usize
    where
        Q: Ord + ?Sized,
        T: Borrow<Q>,
    {
        let (node_idx, position_within_node) = self.locate_value(value);

        let offset = self.index.prefix_sum(node_idx, 0);

        offset + position_within_node
    }
    fn rank_cmp<Q, P>(&self, cmp: P) -> usize
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        P: FnMut(&Q) -> bool,
    {
        let (node_idx, position_within_node) = self.locate_value_cmp(cmp);

        let offset = self.index.prefix_sum(node_idx, 0);

        offset + position_within_node
    }
    pub fn range_idx<R>(&self, range: R) -> Range<'_, T>
    where
        R: RangeBounds<usize>,
    {
        let (
            (global_front_idx, front_node_idx, front_start_idx),
            (global_back_idx, back_node_idx, back_start_idx),
        ) = self.resolve_range(range);

        let front_iter = if front_node_idx < self.inner.len() {
            Some(self.inner[front_node_idx][front_start_idx..].iter())
        } else {
            None
        };

        let back_iter = if back_node_idx < self.inner.len() {
            Some(self.inner[back_node_idx][..=back_start_idx].iter())
        } else {
            None
        };

        Range {
            spine_iter: Iter {
                btree: self,
                current_front_node_idx: front_node_idx,
                current_front_idx: global_front_idx,
                current_back_node_idx: back_node_idx,
                current_back_idx: global_back_idx + 1,
                current_front_iterator: front_iter,
                current_back_iterator: back_iter,
            },
        }
    }
}

impl<T> FromIterator<T> for BTreeSet<T>
where
    T: Ord,
{
    fn from_iter<K: IntoIterator<Item = T>>(iter: K) -> Self {
        let mut btree = BTreeSet::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

impl<T, const N: usize> From<[T; N]> for BTreeSet<T>
where
    T: Ord,
{
    fn from(value: [T; N]) -> Self {
        let mut btree: BTreeSet<T> = Default::default();

        value.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

impl<T> Default for BTreeSet<T>
where
    T: Ord,
{
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE;

        Self {
            inner: vec![Node::with_capacity(node_capacity)],
            index: FenwickTree::from_iter(vec![0]),
            node_capacity,
            len: 0,
        }
    }
}

/// An iterator over the items of a `BTreeSet`.
///
/// This `struct` is created by the [`iter`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`iter`]: BTreeSet::iter
pub struct Iter<'a, T>
where
    T: Ord,
{
    btree: &'a BTreeSet<T>,
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
    pub fn new(btree: &'a BTreeSet<T>) -> Self {
        Self {
            btree,
            current_front_node_idx: 0,
            current_front_idx: 0,
            current_back_node_idx: btree.inner.len() - 1,
            current_back_idx: btree.len(),
            current_front_iterator: Some(btree.inner[0].iter()),
            current_back_iterator: Some(btree.inner[btree.inner.len() - 1].iter()),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: Ord,
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
            if self.current_front_node_idx >= self.btree.inner.len() {
                return None;
            }
            self.current_front_iterator =
                Some(self.btree.inner[self.current_front_node_idx].iter());

            self.next()
        }
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T>
where
    T: Ord,
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
            self.current_back_iterator = Some(self.btree.inner[self.current_back_node_idx].iter());

            self.next_back()
        }
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> where T: Ord {}

impl<'a, T> IntoIterator for &'a BTreeSet<T>
where
    T: Ord,
{
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

/// An owning iterator over the items of a `BTreeSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`BTreeSet`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: BTreeSet#method.into_iter
pub struct IntoIter<T>
where
    T: Ord,
{
    btree: BTreeSet<T>,
}

impl<T> Iterator for IntoIter<T>
where
    T: Ord,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.btree.pop_first()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T>
where
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.btree.pop_last()
    }
}

impl<T> FusedIterator for IntoIter<T> where T: Ord {}

impl<T> IntoIterator for BTreeSet<T>
where
    T: Ord,
{
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        // This will never panic, since there always is at least one node in the btree
        IntoIter { btree: self }
    }
}

struct MergeIter<'a, T>
where
    T: Ord,
{
    start: bool,
    left_iter: Iter<'a, T>,
    current_left: Option<&'a T>,
    right_iter: Iter<'a, T>,
    current_right: Option<&'a T>,
}

impl<'a, T> Iterator for MergeIter<'a, T>
where
    T: Ord,
{
    type Item = (Option<&'a T>, Option<&'a T>);
    fn next(&mut self) -> Option<Self::Item> {
        if !self.start {
            if let Some(left) = self.current_left {
                if let Some(right) = self.current_right {
                    match left.cmp(right) {
                        Ordering::Less => {
                            self.current_left = self.left_iter.next();
                        }
                        Ordering::Equal => {
                            self.current_left = self.left_iter.next();
                            self.current_right = self.right_iter.next();
                        }
                        Ordering::Greater => {
                            self.current_right = self.right_iter.next();
                        }
                    }
                } else {
                    self.current_left = self.left_iter.next();
                }
            } else if let Some(_) = self.current_right {
                self.current_right = self.right_iter.next();
            } else {
                return None;
            }
        } else {
            self.current_left = self.left_iter.next();
            self.current_right = self.right_iter.next();
            self.start = false;
        }

        Some((self.current_left, self.current_right))
    }
}

/// A lazy iterator producing elements in the union of `BTreeSet`s.
///
/// This `struct` is created by the [`union`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`union`]: BTreeSet::union
pub struct Union<'a, T>
where
    T: Ord,
{
    merge_iter: MergeIter<'a, T>,
}

impl<'a, T> Iterator for Union<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((current_left, current_right)) = self.merge_iter.next() {
            return match (current_left, current_right) {
                (Some(left), Some(right)) => {
                    if right < left {
                        Some(right)
                    } else {
                        Some(left)
                    }
                }
                (Some(left), None) => Some(left),
                (None, Some(right)) => Some(right),
                (None, None) => None,
            };
        }

        None
    }
}

impl<'a, T> FusedIterator for Union<'a, T> where T: Ord {}

/// A lazy iterator producing elements in the difference of `BTreeSet`s.
///
/// This `struct` is created by the [`difference`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`difference`]: BTreeSet::difference
pub struct Difference<'a, T>
where
    T: Ord,
{
    merge_iter: MergeIter<'a, T>,
}

impl<'a, T> Iterator for Difference<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return if let Some((current_left, current_right)) = self.merge_iter.next() {
                match (current_left, current_right) {
                    (Some(left), Some(right)) => {
                        if left < right {
                            Some(left)
                        } else {
                            continue;
                        }
                    }
                    (Some(left), None) => Some(left),
                    (None, _) => None,
                }
            } else {
                None
            };
        }
    }
}

impl<'a, T> FusedIterator for Difference<'a, T> where T: Ord {}

/// A lazy iterator producing elements in the symmetric difference of `BTreeSet`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on
/// [`BTreeSet`]. See its documentation for more.
///
/// [`symmetric_difference`]: BTreeSet::symmetric_difference
pub struct SymmetricDifference<'a, T>
where
    T: Ord,
{
    merge_iter: MergeIter<'a, T>,
}

impl<'a, T> Iterator for SymmetricDifference<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            return if let Some((current_left, current_right)) = self.merge_iter.next() {
                match (current_left, current_right) {
                    (Some(left), Some(right)) => {
                        if left < right {
                            Some(left)
                        } else if right < left {
                            Some(right)
                        } else {
                            continue;
                        }
                    }
                    (Some(left), None) => Some(left),
                    (None, Some(right)) => Some(right),
                    (None, _) => None,
                }
            } else {
                None
            };
        }
    }
}

impl<'a, T> FusedIterator for SymmetricDifference<'a, T> where T: Ord {}

/// A lazy iterator producing elements in the intersection of `BTreeSet`s.
///
/// This `struct` is created by the [`intersection`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`intersection`]: BTreeSet::intersection
pub struct Intersection<'a, T>
where
    T: Ord,
{
    merge_iter: MergeIter<'a, T>,
}

impl<'a, T> Iterator for Intersection<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((current_left, current_right)) = self.merge_iter.next() {
                match (current_left, current_right) {
                    (Some(left), Some(right)) => {
                        if left == right {
                            return Some(left);
                        } else {
                            continue;
                        }
                    }
                    (None, _) | (_, None) => return None,
                }
            } else {
                return None;
            }
        }
    }
}

impl<'a, T> FusedIterator for Intersection<'a, T> where T: Ord {}

/// An iterator over a sub-range of items in a `BTreeSet`.
///
/// This `struct` is created by the [`range`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`range`]: BTreeSet::range
pub struct Range<'a, T>
where
    T: Ord,
{
    spine_iter: Iter<'a, T>,
}

impl<'a, T> Iterator for Range<'a, T>
where
    T: Ord,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.spine_iter.next()
    }
}

impl<'a, T> DoubleEndedIterator for Range<'a, T>
where
    T: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.spine_iter.next_back()
    }
}

impl<'a, T> FusedIterator for Range<'a, T> where T: Ord {}

impl<T> Index<usize> for BTreeSet<T>
where
    T: Ord,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get_index(index).unwrap()
    }
}

pub struct VacantEntry<'a, K, V>
where
    K: Ord,
{
    map: &'a mut BTreeMap<K, V>,
    key: K,
}

pub struct OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    map: &'a mut BTreeMap<K, V>,
    idx: usize,
}

pub enum Entry<'a, K, V>
where
    K: 'a + Ord,
    V: 'a,
{
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: 'a + Ord,
    V: 'a,
{
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Vacant(entry) => entry.insert(default),
            Occupied(entry) => entry.into_mut(),
        }
    }
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce() -> V,
    {
        match self {
            Vacant(entry) => entry.insert(default()),
            Occupied(entry) => entry.into_mut(),
        }
    }
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K) -> V,
    {
        match self {
            Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
            Occupied(entry) => entry.into_mut(),
        }
    }
    pub fn key(&self) -> &K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            }
            Vacant(entry) => Vacant(entry),
        }
    }
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    pub fn key(&self) -> &K {
        &self.map.set.get_index(self.idx).unwrap().key
    }
    pub fn remove_entry(self) -> (K, V) {
        self.map.pop_index(self.idx)
    }
    pub fn get(&self) -> &V {
        self.map.get_index(self.idx).unwrap().1
    }
    pub fn get_mut(&mut self) -> &mut V {
        self.map.get_mut_index(self.idx).unwrap()
    }
    pub fn into_mut(self) -> &'a mut V {
        self.map.get_mut_index(self.idx).unwrap()
    }
    pub fn insert(&mut self, value: V) -> V {
        let current_value = self.map.get_mut_index(self.idx).unwrap();
        let mut previous_value = value;
        swap(&mut previous_value, current_value);

        previous_value
    }
    pub fn remove(self) -> V {
        self.map.pop_index(self.idx).1
    }
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Ord,
{
    pub fn key(&self) -> &K {
        &self.key
    }
    pub fn into_key(self) -> K {
        self.key
    }
    pub fn insert(self, value: V) -> &'a mut V {
        let rank = self
            .map
            .set
            .rank_cmp(|item: &Pair<K, V>| &item.key < &self.key);
        self.map.insert(self.key, value);

        self.map.get_mut_index(rank).unwrap()
    }
}

/// An ordered map based on a two-level [B-Tree].
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. In theory, a binary search tree (BST) is the optimal
/// choice for a sorted map, as a perfectly balanced BST performs the theoretical minimum amount of
/// comparisons necessary to find an element (log<sub>2</sub>n). However, in practice the way this
/// is done is *very* inefficient for modern computer architectures. In particular, every element
/// is stored in its own individually heap-allocated node. This means that every single insertion
/// triggers a heap-allocation, and every single comparison should be a cache-miss. Since these
/// are both notably expensive things to do in practice, we are forced to, at the very least,
/// reconsider the BST strategy.
///
/// However, B-Trees are not as performant as they could be, since there still is a significant
/// amount of pointer indirection, and, in Rust's case, a linear search on the node level.
///
/// Our implementation restricts a B-Tree to only have two levels, and have zero pointer indirection,
/// with data residing only in the second level. The first level is an array, sorted by each node's
/// maximum element. The second is where all the data is at, being a sorted array of sorted arrays of
/// fixed size, 1024. Lookups are done in two steps, one binary search over the first level, and one
/// over the second. This is significantly simpler than a regular B-Tree. The main tradeoff, is that
/// insertion and deletion relies on always having to sort an array of size 1024. In practice, this
/// is barely noticable, but still presents itself as a drawback significant enough to warrant considering
/// not using this crate. Please, read the Readme in order to see benchmarking results.
///
/// Furthermore, it has a very efficient get-the-ith-element implementation, that is thousands(literally)
/// of times faster than what is currently available in stdlib.
///
/// Iterators obtained from functions such as [`BTreeMap::iter`], [`BTreeMap::values`], or
/// [`BTreeMap::keys`] produce their items in order by key, and directly leverage Rust's own
/// slice iterators, therefore being as fast as possible.
///
/// [B-Tree]: https://en.wikipedia.org/wiki/B-tree
///
/// # Examples
///
/// ```
/// use indexset::BTreeMap;
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `BTreeMap<&str, &str>` in this example).
/// let mut movie_reviews = BTreeMap::new();
///
/// // review some movies.
/// movie_reviews.insert("Office Space",       "Deals with real issues in the workplace.");
/// movie_reviews.insert("Pulp Fiction",       "Masterpiece.");
/// movie_reviews.insert("The Godfather",      "Very enjoyable.");
/// movie_reviews.insert("The Blues Brothers", "Eye lyked it a lot.");
///
/// // check for a specific one.
/// if !movie_reviews.contains_key("Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              movie_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// movie_reviews.remove("The Blues Brothers");
///
/// // look up the values associated with some keys.
/// let to_find = ["Up!", "Office Space"];
/// for movie in &to_find {
///     match movie_reviews.get(movie) {
///        Some(review) => println!("{movie}: {review}"),
///        None => println!("{movie} is unreviewed.")
///     }
/// }
///
/// // Look up the value for a key (will panic if the key is not found).
/// println!("Movie review: {}", movie_reviews["Office Space"]);
///
/// // iterate over everything.
/// for (movie, review) in &movie_reviews {
///     println!("{movie}: \"{review}\"");
/// }
/// ```
///
/// A `BTreeMap` with a known list of items can be initialized from an array:
///
/// ```
/// use indexset::BTreeMap;
///
/// let solar_distance = BTreeMap::from_iter([
///     ("Mercury", 0.4),
///     ("Venus", 0.7),
///     ("Earth", 1.0),
///     ("Mars", 1.5),
/// ]);
/// ```
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BTreeMap<K, V>
where
    K: Ord,
{
    set: BTreeSet<Pair<K, V>>,
}

impl<K: Ord, V> Default for BTreeMap<K, V>
where
    K: Ord,
{
    fn default() -> Self {
        Self {
            set: BTreeSet::default(),
        }
    }
}

impl<K, V> FromIterator<(K, V)> for BTreeMap<K, V>
where
    K: Ord,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut btree = BTreeMap::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item.0, item.1);
        });

        btree
    }
}

impl<K: Ord, V> BTreeMap<K, V>
where
    K: Ord,
{
    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// If a key from `other` is already present in `self`, the respective
    /// value from `self` will be overwritten with the respective value from `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    /// a.insert(3, "c"); // Note: Key (3) also present in b.
    ///
    /// let mut b = BTreeMap::new();
    /// b.insert(3, "d"); // Note: Key (3) also present in a.
    /// b.insert(4, "e");
    /// b.insert(5, "f");
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    /// assert_eq!(a[&3], "d"); // Note: "c" has been overwritten.
    /// assert_eq!(a[&4], "e");
    /// assert_eq!(a[&5], "f");
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        self.set.append(&mut other.set)
    }
    /// Clears the map, removing all elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.set.clear()
    }
    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.set.contains_cmp(
            |item: &Pair<K, V>| item.key.borrow() < key,
            |item| item.key.borrow() == key,
        )
    }
    /// Returns the first key-value pair in the map.
    /// The key in this pair is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// assert_eq!(map.first_key_value(), None);
    /// map.insert(1, "b");
    /// map.insert(2, "a");
    /// assert_eq!(map.first_key_value(), Some((&1, &"b")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let popping = self.set.first();
        if let Some(pop) = popping {
            return Some((&pop.key, &pop.value));
        }

        None
    }
    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        if let Some(key_value) = self.get_key_value(key) {
            return Some(key_value.1);
        }

        None
    }
    /// Returns the key-value pair currently residing at the given position.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_index(0), Some((&1, &"a")));
    /// assert_eq!(map.get_index(1), None);
    /// ```
    pub fn get_index(&self, idx: usize) -> Option<(&K, &V)> {
        let ith = self.set.get_index(idx);
        if let Some(entry) = ith {
            return Some((&entry.key, &entry.value));
        }

        None
    }
    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (node_idx, position_within_node) = self
            .set
            .locate_value_cmp(|item: &Pair<K, V>| item.key.borrow() < key);
        if let Some(candidate_node) = self.set.inner.get(node_idx) {
            if let Some(candidate_value) = candidate_node.get(position_within_node) {
                if candidate_value.key.borrow() == key {
                    return Some((&candidate_value.key, &candidate_value.value));
                }
            }
        }

        None
    }
    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        let (node_idx, position_within_node) = self
            .set
            .locate_value_cmp(|item: &Pair<K, V>| item.key.borrow() < key);
        if self.set.inner.get(node_idx).is_some()
            && self.set.inner[node_idx].get(position_within_node).is_some()
        {
            let entry = self.set.inner[node_idx].get_mut(position_within_node)?;
            if key == entry.key.borrow() {
                return Some(&mut entry.value);
            }
        }

        None
    }
    /// Returns a mutable reference to the value at the designated index
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut_index(0) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut_index(&mut self, index: usize) -> Option<&mut V> {
        if let Some(entry) = self.set.get_mut_index(index) {
            return Some(&mut entry.value);
        }

        None
    }
    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical. See the [module-level
    /// documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.contains_key(&key) {
            let old_entry = self
                .set
                .delete_cmp(|item: &Pair<K, V>| item.key < key, |item| item.key == key)
                .0?;

            self.set.insert(Pair { key, value });

            Some(old_entry.value)
        } else {
            self.set.insert(Pair { key, value });

            None
        }
    }
    /// Creates a consuming iterator visiting all the keys, in sorted order.
    /// The map cannot be used after calling this.
    /// The iterator element type is `K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(2, "b");
    /// a.insert(1, "a");
    ///
    /// let keys: Vec<i32> = a.into_keys().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            inner: self.into_iter(),
        }
    }
    /// Creates a consuming iterator visiting all the values, in order by key.
    /// The map cannot be used after calling this.
    /// The iterator element type is `V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "hello");
    /// a.insert(2, "goodbye");
    ///
    /// let values: Vec<&str> = a.into_values().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            inner: self.into_iter(),
        }
    }
    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(3, "c");
    /// map.insert(2, "b");
    /// map.insert(1, "a");
    ///
    /// for (key, value) in map.iter() {
    ///     println!("{key}: {value}");
    /// }
    ///
    /// let (first_key, first_value) = map.iter().next().unwrap();
    /// assert_eq!((*first_key, *first_value), (1, "a"));
    /// ```
    pub fn iter(&self) -> IterMap<K, V> {
        IterMap {
            inner: self.set.iter(),
        }
    }
    /// Gets a mutable iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::from_iter([
    ///    ("a", 1),
    ///    ("b", 2),
    ///    ("c", 3),
    /// ]);
    ///
    /// // add 10 to the value if the key isn't "a"
    /// for (key, value) in map.iter_mut() {
    ///     if key != &"a" {
    ///         *value += 10;
    ///     }
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        let last_node_idx = self.set.inner.len() - 1;
        let len = self.set.len();

        // Special handling for single node case
        if self.set.inner.len() == 1 {
            // Don't consume the node from inner iterator
            // Both front and back should start from the same node
            let mut inner = self.set.inner.iter_mut();
            let node = inner.next().unwrap();
            let front_iter = node.iter_mut();
            // For single node, back_iter should be empty initially
            // The iterator logic will handle switching to it when needed
            let back_iter = [].iter_mut();

            return IterMut {
                inner,
                current_front_node_idx: 0,
                current_front_idx: 0,
                current_back_node_idx: 0,  // Same as front for single node
                current_back_idx: len.wrapping_sub(1),
                current_front_iterator: front_iter,
                current_back_iterator: back_iter,
            };
        }

        // For multiple nodes, handle normally
        let mut inner = self.set.inner.iter_mut();
        let front_iter = if let Some(node) = inner.next() {
            node.iter_mut()
        } else {
            [].iter_mut()
        };
        let back_iter = if let Some(node) = inner.next_back() {
            node.iter_mut()
        } else {
            [].iter_mut()
        };

        IterMut {
            inner,
            current_front_node_idx: 0,
            current_front_idx: 0,
            current_back_node_idx: last_node_idx,
            current_back_idx: len.wrapping_sub(1),
            current_front_iterator: front_iter,
            current_back_iterator: back_iter,
        }
    }
    /// Gets an iterator over the keys of the map, in sorted order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(2, "b");
    /// a.insert(1, "a");
    ///
    /// let keys: Vec<_> = a.keys().cloned().collect();
    /// assert_eq!(keys, [1, 2]);
    /// ```
    pub fn keys(&self) -> Keys<K, V> {
        Keys {
            inner: self.set.iter(),
        }
    }
    /// Returns the last key-value pair in the map.
    /// The key in this pair is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "b");
    /// map.insert(2, "a");
    /// assert_eq!(map.last_key_value(), Some((&2, &"a")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let popping = self.set.last();
        if let Some(pop) = popping {
            return Some((&pop.key, &pop.value));
        }

        None
    }
    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.set.len()
    }
    /// Makes a new, empty `BTreeMap`.
    ///
    /// Allocates a vec of capacity 1024.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new() -> Self {
        Self {
            ..Default::default()
        }
    }
    /// Makes a new, empty `BTreeSet` with the given maximum node size. Allocates one vec with
    /// the capacity set to be the specified node size.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// use indexset::BTreeMap;
    ///
    /// let mut set: BTreeMap<usize, usize> = BTreeMap::with_maximum_node_size(128);
    pub fn with_maximum_node_size(maximum_node_size: usize) -> Self {
        Self {
            set: BTreeSet::with_maximum_node_size(maximum_node_size),
        }
    }
    /// Removes and returns the first element in the map.
    /// The key of this element is the minimum key that was in the map.
    ///
    /// # Examples
    ///
    /// Draining elements in ascending order, while keeping a usable map each iteration.
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// while let Some((key, _val)) = map.pop_first() {
    ///     assert!(map.iter().all(|(k, _v)| *k > key));
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        let popping = self.set.pop_first();
        if let Some(pop) = popping {
            return Some((pop.key, pop.value));
        }

        None
    }
    /// Removes the i-th element from the map and returns it, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::{BTreeMap};
    ///
    /// let mut map = BTreeMap::new();
    ///
    /// map.insert(1,"a");
    /// map.insert(2, "b");
    /// assert_eq!(map.pop_index(0), (1, "a"));
    /// assert_eq!(map.pop_index(0), (2, "b"));
    /// assert!(map.is_empty());
    /// ```
    pub fn pop_index(&mut self, index: usize) -> (K, V) {
        let popping = self.set.pop_index(index);

        (popping.key, popping.value)
    }
    /// Removes and returns the last element in the map.
    /// The key of this element is the maximum key that was in the map.
    ///
    /// # Examples
    ///
    /// Draining elements in descending order, while keeping a usable map each iteration.
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// while let Some((key, _val)) = map.pop_last() {
    ///     assert!(map.iter().all(|(k, _v)| *k < key));
    /// }
    /// assert!(map.is_empty());
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        let popping = self.set.pop_last();
        if let Some(pop) = popping {
            return Some((pop.key, pop.value));
        }

        None
    }
    /// Constructs a double-ended iterator over a sub-range of elements in the map.
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
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(3, "a");
    /// map.insert(5, "b");
    /// map.insert(8, "c");
    /// for (&key, &value) in map.range((Included(&4), Included(&8))) {
    ///     println!("{key}: {value}");
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(4..).next());
    /// ```
    pub fn range<Q, R>(&self, range: R) -> RangeMap<K, V>
    where
        Q: Ord + ?Sized,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        let (start_idx, end_idx) = self.range_to_idx(range);

        RangeMap {
            inner: self.set.range_idx(start_idx..=end_idx),
        }
    }
    pub fn range_idx<R>(&self, range: R) -> RangeMap<K, V>
    where
        R: RangeBounds<usize>,
    {
        RangeMap {
            inner: self.set.range_idx(range),
        }
    }
    fn range_to_idx<Q, R>(&self, range: R) -> (usize, usize)
    where
        Q: Ord + ?Sized,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        let start_idx = match range.start_bound() {
            Bound::Included(bound) => self
                .set
                .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < bound),
            Bound::Excluded(bound) => self
                .set
                .rank_cmp(|item: &Pair<K, V>| item.key.borrow() <= bound),
            Bound::Unbounded => 0,
        };
        let end_idx = match range.end_bound() {
            Bound::Included(bound) => self
                .set
                .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < bound),
            Bound::Excluded(bound) => {
                let rank = self
                    .set
                    .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < bound);
                if rank == 0 {
                    // No elements before this bound, return empty range
                    return (1, 0);
                }
                rank - 1
            }
            Bound::Unbounded => {
                if self.len() == 0 {
                    // Empty map, return empty range
                    return (1, 0);
                }
                self.len() - 1
            }
        };

        (start_idx, end_idx)
    }
    /// Constructs a mutable double-ended iterator over a sub-range of elements in the map.
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
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map: BTreeMap<&str, i32> =
    ///     [("Alice", 0), ("Bob", 0), ("Carol", 0), ("Cheryl", 0)].into();
    /// for (_, balance) in map.range_mut("B".."Cheryl") {
    ///     *balance += 100;
    /// }
    /// for (name, balance) in &map {
    ///     println!("{name} => {balance}");
    /// }
    /// ```
    pub fn range_mut<Q, R>(&mut self, range: R) -> RangeMut<K, V>
    where
        Q: Ord + ?Sized,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        let (start_idx, end_idx) = self.range_to_idx(range);

        self.range_mut_idx(start_idx..=end_idx)
    }
    pub fn range_mut_idx<R>(&mut self, range: R) -> RangeMut<K, V>
    where
        R: RangeBounds<usize>,
    {
        let (
            (global_front_idx, front_node_idx, front_start_idx),
            (global_back_idx, back_node_idx, back_start_idx),
        ) = self.set.resolve_range(range);
        let end = self.set.inner[back_node_idx].len();

        let mut inner = self.set.inner.iter_mut();

        let mut front_iter = {
            if let Some(node) = inner.nth(front_node_idx) {
                node.iter_mut()
            } else {
                [].iter_mut()
            }
        };

        let mut back_iter = {
            if let Some(node) = inner.nth(back_node_idx - front_node_idx) {
                node.iter_mut()
            } else {
                [].iter_mut()
            }
        };

        for _ in 0..front_start_idx {
            front_iter.next();
        }
        let offset = back_node_idx - front_node_idx;
        if offset > 0 {
            for _ in back_start_idx..end {
                back_iter.next_back();
            }
        } else {
            for _ in back_start_idx..end {
                front_iter.next_back();
            }
        }

        RangeMut {
            inner: IterMut {
                inner,
                current_front_node_idx: front_node_idx,
                current_front_idx: global_front_idx,
                current_back_node_idx: back_node_idx,
                current_back_idx: global_back_idx,
                current_front_iterator: front_iter,
                current_back_iterator: back_iter,
            },
        }
    }
    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let old_entry = self.set.delete_cmp(
            |item: &Pair<K, V>| item.key.borrow() < key,
            |item: &Pair<K, V>| item.key.borrow() == key,
        );

        if old_entry.1 {
            return Some(old_entry.0?.value);
        }

        None
    }
    /// Removes a key from the map, returning the stored key and value if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        let old_entry = self.set.delete_cmp(
            |item: &Pair<K, V>| item.key.borrow() < key,
            |item| item.key.borrow() == key,
        );

        if old_entry.1 {
            let key_value = old_entry.0?;
            return Some((key_value.key, key_value.value));
        }

        None
    }
    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    /// The elements are visited in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut map: BTreeMap<i32, i32> = (0..8).map(|x| (x, x*10)).collect();
    /// // Keep only the elements with even-numbered keys.
    /// map.retain(|&k, _| k % 2 == 0);
    /// assert!(map.into_iter().eq(vec![(0, 0), (2, 20), (4, 40), (6, 60)]));
    /// ```
    pub fn retain<F, Q>(&mut self, mut f: F)
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
        F: FnMut(&Q, &mut V) -> bool,
    {
        let mut positions_to_delete = vec![];
        for (node_idx, node) in self.set.inner.iter_mut().enumerate() {
            for (position_within_node, item) in node.iter_mut().enumerate() {
                if !f(item.key.borrow(), &mut item.value) {
                    positions_to_delete.push((node_idx, position_within_node));
                }
            }
        }

        positions_to_delete.reverse();

        positions_to_delete
            .into_iter()
            .for_each(|(node_idx, position_within_node)| {
                self.set.delete_at(node_idx, position_within_node);
            })
    }
    /// Splits the collection into two at the given key. Returns everything after the given key,
    /// including the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    /// a.insert(3, "c");
    /// a.insert(17, "d");
    /// a.insert(41, "e");
    ///
    /// let b = a.split_off(&3);
    ///
    /// assert_eq!(a.len(), 2);
    /// assert_eq!(b.len(), 3);
    ///
    /// assert_eq!(a[&1], "a");
    /// assert_eq!(a[&2], "b");
    ///
    /// assert_eq!(b[&3], "c");
    /// assert_eq!(b[&17], "d");
    /// assert_eq!(b[&41], "e");
    /// ```
    pub fn split_off<Q>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        BTreeMap {
            set: self
                .set
                .split_off_cmp(|item: &Pair<K, V>| item.key.borrow() < key),
        }
    }
    /// Gets an iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "hello");
    /// a.insert(2, "goodbye");
    ///
    /// let values: Vec<&str> = a.values().cloned().collect();
    /// assert_eq!(values, ["hello", "goodbye"]);
    /// ```
    pub fn values(&self) -> Values<K, V> {
        Values {
            inner: self.set.iter(),
        }
    }
    /// Gets a mutable iterator over the values of the map, in order by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, String::from("hello"));
    /// a.insert(2, String::from("goodbye"));
    ///
    /// for value in a.values_mut() {
    ///     value.push_str("!");
    /// }
    ///
    /// let values: Vec<String> = a.values().cloned().collect();
    /// assert_eq!(values, [String::from("hello!"),
    ///                     String::from("goodbye!")]);
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut {
            inner: self.iter_mut(),
        }
    }
    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut count: BTreeMap<&str, usize> = BTreeMap::new();
    ///
    /// // count the number of occurrences of letters in the vec
    /// for x in ["a", "b", "a", "c", "a", "b"] {
    ///     count.entry(x).and_modify(|curr| *curr += 1).or_insert(1);
    /// }
    ///
    /// assert_eq!(count["a"], 3);
    /// assert_eq!(count["b"], 2);
    /// assert_eq!(count["c"], 1);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V>
    where
        K: Ord,
    {
        if self.contains_key(&key) {
            let idx = self.set.rank_cmp(|item: &Pair<K, V>| item.key < key);
            return Occupied(OccupiedEntry { map: self, idx });
        }

        Vacant(VacantEntry { map: self, key })
    }
    /// Returns the first entry in the map for in-place manipulation.
    /// The key of this entry is the minimum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// if let Some(mut entry) = map.first_entry() {
    ///     if *entry.key() > 0 {
    ///         entry.insert("first");
    ///     }
    /// }
    /// assert_eq!(*map.get(&1).unwrap(), "first");
    /// assert_eq!(*map.get(&2).unwrap(), "b");
    /// ```
    pub fn first_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>>
    where
        K: Ord,
    {
        if !self.is_empty() {
            return Some(OccupiedEntry { map: self, idx: 0 });
        }

        None
    }
    /// Returns the last entry in the map for in-place manipulation.
    /// The key of this entry is the maximum key in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// if let Some(mut entry) = map.last_entry() {
    ///     if *entry.key() > 0 {
    ///         entry.insert("last");
    ///     }
    /// }
    /// assert_eq!(*map.get(&1).unwrap(), "a");
    /// assert_eq!(*map.get(&2).unwrap(), "last");
    /// ```
    pub fn last_entry(&mut self) -> Option<OccupiedEntry<'_, K, V>>
    where
        K: Ord,
    {
        let len = self.len();
        if len > 0 {
            return Some(OccupiedEntry {
                map: self,
                idx: len - 1,
            });
        }

        None
    }
    /// Returns a [`Cursor`] pointing at the first element that is above the
    /// given bound.
    ///
    /// If no such element exists then a cursor pointing at the "ghost"
    /// non-element is returned.
    ///
    /// Passing [`Bound::Unbounded`] will return a cursor pointing at the first
    /// element of the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::BTreeMap;
    /// use std::ops::Bound;
    ///
    /// let mut a = BTreeMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    /// a.insert(3, "c");
    /// a.insert(4, "c");
    /// let cursor = a.lower_bound(Bound::Excluded(&2));
    /// assert_eq!(cursor.key(), Some(&3));
    /// ```
    pub fn lower_bound<Q>(&self, bound: Bound<&Q>) -> CursorMap<'_, K, V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        let start_idx = match bound {
            Bound::Included(start) => self
                .set
                .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < start),
            Bound::Excluded(start) => {
                self.set
                    .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < start)
                    + 1
            }
            Bound::Unbounded => 0,
        };

        CursorMap {
            cursor: Cursor {
                set: &self.set,
                idx: start_idx,
            },
        }
    }
    /// Returns the position in which the given element would fall in the already-existing sorted
    /// order.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use indexset::BTreeMap;
    ///
    /// let set = BTreeMap::from_iter([(1, "a"), (2, "b"), (3, "c")]);
    /// assert_eq!(set.rank(&1), 0);
    /// assert_eq!(set.rank(&3), 2);
    /// assert_eq!(set.rank(&4), 3);
    /// assert_eq!(set.rank(&100), 3);
    /// ```
    pub fn rank<Q>(&self, value: &Q) -> usize
    where
        Q: Ord + ?Sized,
        K: Borrow<Q>,
    {
        self.set
            .rank_cmp(|item: &Pair<K, V>| item.key.borrow() < value)
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for BTreeMap<K, V>
where
    K: Ord,
{
    fn from(value: [(K, V); N]) -> Self {
        let mut btree: BTreeMap<K, V> = Default::default();

        value.into_iter().for_each(|(key, value)| {
            btree.insert(key, value);
        });

        btree
    }
}

impl<K, V> IntoIterator for BTreeMap<K, V>
where
    K: Ord,
{
    type Item = (K, V);
    type IntoIter = IntoIterMap<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIterMap {
            inner: self.set.into_iter(),
        }
    }
}

impl<'a, K, V> IntoIterator for &'a BTreeMap<K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);

    type IntoIter = IterMap<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMap {
            inner: self.set.iter(),
        }
    }
}

/// An iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`iter`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter`]: BTreeMap::iter
pub struct IterMap<'a, K, V>
where
    K: Ord,
{
    inner: Iter<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for IterMap<'a, K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMap<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> FusedIterator for IterMap<'a, K, V> where K: Ord {}

/// An owning iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`into_iter`] method on [`BTreeMap`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: IntoIterator::into_iter
pub struct IntoIterMap<K, V>
where
    K: Ord,
{
    inner: IntoIter<Pair<K, V>>,
}

impl<K, V> Iterator for IntoIterMap<K, V>
where
    K: Ord,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((entry.key, entry.value));
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for IntoIterMap<K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((entry.key, entry.value));
        }

        None
    }
}

impl<K, V> FusedIterator for IntoIterMap<K, V> where K: Ord {}

/// An owning iterator over the keys of a `BTreeMap`.
///
/// This `struct` is created by the [`into_keys`] method on [`BTreeMap`].
/// See its documentation for more.
///
/// [`into_keys`]: BTreeMap::into_keys
pub struct IntoKeys<K, V>
where
    K: Ord,
{
    inner: IntoIterMap<K, V>,
}

impl<K, V> Iterator for IntoKeys<K, V>
where
    K: Ord,
{
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some(entry.0);
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for IntoKeys<K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some(entry.0);
        }

        None
    }
}

impl<K, V> FusedIterator for IntoKeys<K, V> where K: Ord {}

/// An owning iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`into_values`] method on [`BTreeMap`].
/// See its documentation for more.
///
/// [`into_values`]: BTreeMap::into_values
pub struct IntoValues<K, V>
where
    K: Ord,
{
    inner: IntoIterMap<K, V>,
}

impl<K, V> Iterator for IntoValues<K, V>
where
    K: Ord,
{
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some(entry.1);
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for IntoValues<K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some(entry.1);
        }

        None
    }
}

impl<K, V> FusedIterator for IntoValues<K, V> where K: Ord {}

/// An iterator over a sub-range of entries in a `BTreeMap`.
///
/// This `struct` is created by the [`range`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`range`]: BTreeMap::range
pub struct RangeMap<'a, K, V>
where
    K: Ord,
{
    inner: Range<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for RangeMap<'a, K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for RangeMap<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> FusedIterator for RangeMap<'a, K, V> where K: Ord {}

/// An iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`values`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`values`]: BTreeMap::values
pub struct Values<'a, K, V>
where
    K: Ord,
{
    inner: Iter<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Values<'a, K, V>
where
    K: Ord,
{
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some(&entry.value);
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some(&entry.value);
        }

        None
    }
}

impl<'a, K, V> FusedIterator for Values<'a, K, V> where K: Ord {}

/// An iterator over the keys of a `BTreeMap`.
///
/// This `struct` is created by the [`keys`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`keys`]: BTreeMap::keys
pub struct Keys<'a, K, V>
where
    K: Ord,
{
    inner: Iter<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V>
where
    K: Ord,
{
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some(&entry.key);
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some(&entry.key);
        }

        None
    }
}

impl<'a, K, V> FusedIterator for Keys<'a, K, V> where K: Ord {}

/// A mutable iterator over the entries of a `BTreeMap`.
///
/// This `struct` is created by the [`iter_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`iter_mut`]: BTreeMap::iter_mut
pub struct IterMut<'a, K: 'a, V: 'a>
where
    K: Ord,
{
    inner: std::slice::IterMut<'a, Node<Pair<K, V>>>,
    current_front_node_idx: usize,
    current_front_idx: usize,
    current_back_node_idx: usize,
    current_back_idx: usize,
    current_front_iterator: std::slice::IterMut<'a, Pair<K, V>>,
    current_back_iterator: std::slice::IterMut<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_front_idx == self.current_back_idx.wrapping_add(1) {
            return None;
        }
        if let Some(entry) = self.current_front_iterator.next() {
            self.current_front_idx += 1;
            return Some((&entry.key, &mut entry.value));
        } else {
            // If the current iterator has been exhausted, we have to check whether there are any
            // iterators left
            if self.current_front_node_idx == self.inner.size_hint().0 {
                return None;
            }
            if self.current_front_node_idx == self.current_back_node_idx - 1 {
                // take from the current back iter
                if let Some(entry) = self.current_back_iterator.next() {
                    self.current_front_idx += 1;
                    return Some((&entry.key, &mut entry.value));
                }
            } else {
                // advance front
                self.current_front_node_idx += 1;
                if let Some(node) = self.inner.next() {
                    self.current_front_iterator = node.iter_mut();
                }

                return self.next();
            }
        };

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.current_front_idx == self.current_back_idx.wrapping_add(1) {
            return None;
        }
        if let Some(entry) = self.current_back_iterator.next_back() {
            self.current_back_idx -= 1;
            return Some((&entry.key, &mut entry.value));
        } else {
            // If the current iterator has been exhausted, we have to check whether there are any
            // iterators left
            if self.current_back_node_idx == 0 && self.current_front_node_idx != 0 {
                return None;
            }
            // Handle single node case or adjacent nodes
            if self.current_front_node_idx == self.current_back_node_idx ||
               self.current_front_node_idx == self.current_back_node_idx - 1 {
                // take from the current front iter
                if let Some(entry) = self.current_front_iterator.next_back() {
                    if self.current_back_idx > 0 {
                        self.current_back_idx -= 1;
                    }
                    return Some((&entry.key, &mut entry.value));
                }
            } else {
                // advance back
                self.current_back_node_idx -= 1;
                if let Some(node) = self.inner.next_back() {
                    self.current_back_iterator = node.iter_mut();
                }

                return self.next_back();
            }
        };

        None
    }
}

impl<'a, K, V> FusedIterator for IterMut<'a, K, V> where K: Ord {}

/// A mutable iterator over the values of a `BTreeMap`.
///
/// This `struct` is created by the [`values_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`values_mut`]: BTreeMap::values_mut
pub struct ValuesMut<'a, K: 'a, V: 'a>
where
    K: Ord,
{
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V>
where
    K: Ord,
{
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some(entry.1);
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for ValuesMut<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some(entry.1);
        }

        None
    }
}

impl<'a, K, V> FusedIterator for ValuesMut<'a, K, V> where K: Ord {}

/// A mutable iterator over a sub-range of entries in a `BTreeMap`.
///
/// This `struct` is created by the [`range_mut`] method on [`BTreeMap`]. See its
/// documentation for more.
///
/// [`range_mut`]: BTreeMap::range_mut
pub struct RangeMut<'a, K: 'a, V: 'a>
where
    K: Ord,
{
    inner: IterMut<'a, K, V>,
}

impl<'a, K, V> Iterator for RangeMut<'a, K, V>
where
    K: Ord,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K, V> DoubleEndedIterator for RangeMut<'a, K, V>
where
    K: Ord,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, K, V> FusedIterator for RangeMut<'a, K, V> where K: Ord {}

impl<K, Q, V> Index<&Q> for BTreeMap<K, V>
where
    K: Borrow<Q> + Ord,

    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}

pub struct Cursor<'a, T>
where
    T: Ord,
{
    set: &'a BTreeSet<T>,
    idx: usize,
}

impl<'a, T: Ord> Cursor<'a, T> {
    pub fn move_next(&mut self) {
        if self.idx == self.set.len() {
            self.idx = 0
        } else {
            self.idx += 1;
        }
    }
    pub fn move_index(&mut self, index: usize) {
        self.idx = index
    }
    pub fn move_prev(&mut self) {
        if self.idx == 0 {
            self.idx = self.set.len()
        } else {
            self.idx -= 1;
        }
    }
    pub fn item(&self) -> Option<&'a T> {
        self.set.get_index(self.idx)
    }
    pub fn peek_next(&self) -> Option<&'a T> {
        if self.idx == self.set.len() {
            return self.set.first();
        }

        self.set.get_index(self.idx + 1)
    }
    pub fn peek_index(&self, index: usize) -> Option<&'a T> {
        self.set.get_index(index)
    }
    pub fn peek_prev(&self) -> Option<&'a T> {
        if self.idx == 0 {
            return None;
        }

        self.set.get_index(self.idx - 1)
    }
}

pub struct CursorMap<'a, K, V>
where
    K: 'a + Ord,
    V: 'a,
{
    cursor: Cursor<'a, Pair<K, V>>,
}

impl<'a, K: Ord, V> CursorMap<'a, K, V> {
    pub fn move_next(&mut self) {
        self.cursor.move_next()
    }
    pub fn move_index(&mut self, index: usize) {
        self.cursor.move_index(index)
    }
    pub fn move_prev(&mut self) {
        self.cursor.move_prev()
    }
    pub fn key(&self) -> Option<&'a K> {
        if let Some(entry) = self.cursor.item() {
            return Some(&entry.key);
        }

        None
    }
    pub fn value(&self) -> Option<&'a V> {
        if let Some(entry) = self.cursor.item() {
            return Some(&entry.value);
        }

        None
    }
    pub fn key_value(&self) -> Option<(&'a K, &'a V)> {
        if let Some(entry) = self.cursor.item() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
    pub fn peek_next(&self) -> Option<(&'a K, &'a V)> {
        if let Some(entry) = self.cursor.peek_next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
    pub fn peek_index(&self, index: usize) -> Option<(&'a K, &'a V)> {
        if let Some(entry) = self.cursor.peek_index(index) {
            return Some((&entry.key, &entry.value));
        }

        None
    }
    pub fn peek_prev(&self) -> Option<(&'a K, &'a V)> {
        if let Some(entry) = self.cursor.peek_prev() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::core::constants::*;
    use super::core::node::*;
    use crate::{BTreeMap, BTreeSet, Node};
    use rand::{Rng, SeedableRng};
    use std::collections::Bound::Included;

    #[test]
    fn test_insert() {
        let input: Vec<isize> = vec![1, 9, 2, 7, 6, 3, 5, 4, 10, 8];

        let expected_output: Vec<isize> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let actual_node =
            input
                .iter()
                .fold(Node::with_capacity(DEFAULT_INNER_SIZE), |mut acc, curr| {
                    NodeLike::insert(&mut acc, *curr);
                    acc
                });

        let actual_output: Vec<isize> = actual_node.iter().cloned().collect();

        assert_eq!(expected_output, actual_output);
        assert_eq!(*actual_node.last().unwrap(), 10);
    }

    #[test]
    fn test_halve() {
        let mut input: Vec<isize> = vec![];
        for item in 0..DEFAULT_INNER_SIZE {
            input.push(item.clone() as isize);
        }

        let mut former_node = Node::with_capacity(DEFAULT_INNER_SIZE);
        input.iter().for_each(|item| {
            NodeLike::insert(&mut former_node, item.clone());
        });
        let latter_node = former_node.halve();

        let expected_former_output: Vec<isize> = input[0..DEFAULT_CUTOFF].to_vec();
        let expected_latter_output: Vec<isize> = input[DEFAULT_CUTOFF..].to_vec();

        let actual_former_output: Vec<isize> = former_node.iter().cloned().collect();
        let actual_latter_output: Vec<isize> = latter_node.iter().cloned().collect();

        assert_eq!(expected_former_output, actual_former_output);
        assert_eq!(expected_latter_output, actual_latter_output);
    }

    #[test]
    fn test_insert_btree() {
        // This will cause the btree to have at least more than one node
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).into_iter().rev().collect();
        let expected_output: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).collect();

        let btree: BTreeSet<usize> = input.into_iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr);
            acc
        });
        assert!(btree.inner.len() > 1);

        let actual_output: Vec<usize> = btree.into_iter().collect();

        assert_eq!(expected_output, actual_output);
    }

    #[test]
    fn test_insert_duplicates() {
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1))
            .into_iter()
            .rev()
            .cycle()
            .take(DEFAULT_INNER_SIZE * 3)
            .collect();
        let expected_output: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).collect();

        let btree: BTreeSet<usize> = input.into_iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr);
            acc
        });
        assert!(btree.inner.len() > 1);

        let actual_output: Vec<usize> = btree.into_iter().collect();

        assert_eq!(expected_output.len(), actual_output.len());
        assert_eq!(expected_output, actual_output);
    }

    #[test]
    fn test_remove() {
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).into_iter().collect();

        let mut btree: BTreeSet<usize> = input.iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr.clone());
            acc
        });

        input.iter().for_each(|item| {
            assert!(btree.remove(item));
        });

        let actual_output: Vec<usize> = btree.into_iter().collect();
        let expected_output: Vec<usize> = vec![];

        assert_eq!(expected_output, actual_output);
    }

    #[test]
    fn test_take() {
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).into_iter().collect();

        let mut btree: BTreeSet<usize> = input.iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr.clone());
            acc
        });

        input.iter().for_each(|item| {
            assert_eq!(*item, btree.take(item).unwrap());
        });

        let actual_output: Vec<usize> = btree.into_iter().collect();
        let expected_output: Vec<usize> = vec![];

        assert_eq!(expected_output, actual_output);
    }

    #[test]
    fn test_first_last_with_pop() {
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).into_iter().collect();

        let btree: BTreeSet<usize> = input.iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr.clone());
            acc
        });

        let mut front_spine = btree.clone();
        let mut back_spine = btree.clone();
        btree.iter().for_each(|item| {
            if *item < DEFAULT_INNER_SIZE {
                assert_eq!(front_spine.get_index(0), front_spine.first());
                assert_eq!(
                    front_spine.pop_first().unwrap() + 1,
                    *front_spine.first().unwrap()
                );
            } else {
                assert_eq!(front_spine.pop_first().unwrap(), DEFAULT_INNER_SIZE);
                assert_eq!(front_spine.first(), None);
            }
        });

        input.iter().rev().for_each(|item| {
            if *item > 0 {
                assert_eq!(
                    back_spine.get_index(back_spine.len() - 1),
                    back_spine.last()
                );
                assert_eq!(
                    back_spine.pop_last().unwrap() - 1,
                    *back_spine.last().unwrap()
                );
            } else {
                assert_eq!(back_spine.pop_last(), Some(0));
                assert_eq!(back_spine.last(), None);
            }
        });
    }

    #[test]
    fn test_map_get() {
        let btree = BTreeMap::from_iter((0..(DEFAULT_INNER_SIZE * 10)).map(|i| (i, i)));

        assert_eq!(btree.len(), DEFAULT_INNER_SIZE * 10);

        for item in 0..DEFAULT_INNER_SIZE * 10 {
            assert_eq!(btree.get(&item), Some(&item));
        }
    }

    #[test]
    fn test_get_contains_lower_bound() {
        let input: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).into_iter().rev().collect();
        let expected_output: Vec<usize> = (0..(DEFAULT_INNER_SIZE + 1)).collect();

        let btree: BTreeSet<usize> = input.iter().fold(BTreeSet::new(), |mut acc, curr| {
            acc.insert(curr.clone());
            acc
        });

        expected_output.into_iter().for_each(|item| {
            assert_eq!(*btree.get_index(item).unwrap(), item);
            assert_eq!(
                *btree.get_index(item).unwrap(),
                *btree.lower_bound(&item).unwrap()
            );
            assert!(btree.contains(&item));
        });
    }

    #[test]
    fn test_iter() {
        let btree = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE * 10)).rev());
        assert_eq!(btree.inner.len(), 19);
        let expected_forward = Vec::from_iter(0..(DEFAULT_INNER_SIZE * 10));
        let actual_forward = Vec::from_iter(btree.iter().cloned());
        assert_eq!(expected_forward, actual_forward);
        let expected_backward = Vec::from_iter((0..(DEFAULT_INNER_SIZE * 10)).rev());
        let actual_backward = Vec::from_iter(btree.iter().cloned().rev());
        assert_eq!(expected_backward, actual_backward);
    }

    #[test]
    fn test_iter_mut() {
        let btree = BTreeMap::from_iter((0..(DEFAULT_INNER_SIZE * 10)).enumerate().rev());
        assert_eq!(btree.set.inner.len(), 19);
        let expected_forward = Vec::from_iter((0..(DEFAULT_INNER_SIZE * 10)).enumerate());
        btree
            .clone()
            .iter_mut()
            .zip(expected_forward)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });

        let expected_backward = Vec::from_iter((0..(DEFAULT_INNER_SIZE * 10)).enumerate().rev());
        btree
            .clone()
            .iter_mut()
            .rev()
            .zip(expected_backward)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
    }

    #[test]
    fn test_into_iter() {
        let btree = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE * 10)).rev());
        assert_eq!(btree.inner.len(), 19);
        let expected_forward = Vec::from_iter(0..(DEFAULT_INNER_SIZE * 10));
        let actual_forward = Vec::from_iter(btree.clone().into_iter());
        assert_eq!(expected_forward, actual_forward);
        let expected_backward = Vec::from_iter((0..(DEFAULT_INNER_SIZE * 10)).rev());
        let actual_backward = Vec::from_iter(btree.into_iter().rev());
        assert_eq!(expected_backward, actual_backward);
    }

    #[test]
    fn test_range() {
        let btree = BTreeSet::from_iter(0..10);
        let first_to_second: Vec<usize> = (1..2).collect();
        let three_til_end: Vec<usize> = (3..10).collect();
        let start_til_four: Vec<usize> = (0..4).collect();
        let start_til_end: Vec<usize> = (0..10).collect();
        let five_til_six_included: Vec<usize> = (5..=6).collect();
        let start_til_seven_included: Vec<usize> = (0..=7).collect();
        assert_eq!(
            Vec::from_iter(btree.range_idx(..).cloned()),
            Vec::from_iter(btree.iter().cloned())
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(0..).cloned()),
            Vec::from_iter(btree.iter().cloned())
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(0..10).cloned()),
            Vec::from_iter(btree.iter().cloned())
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(..10).cloned()),
            Vec::from_iter(btree.iter().cloned())
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(1..2).cloned()),
            first_to_second
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(3..10).cloned()),
            three_til_end
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(0..4).cloned()),
            start_til_four
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(0..10).cloned()),
            start_til_end
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(5..=6).cloned()),
            five_til_six_included
        );
        assert_eq!(
            Vec::from_iter(btree.range_idx(0..=7).cloned()),
            start_til_seven_included
        );
    }

    #[test]
    fn test_range_mut() {
        let btree = BTreeMap::from_iter((0..10).into_iter().enumerate());
        btree
            .clone()
            .range_mut_idx(..)
            .zip(btree.iter())
            .for_each(|(lhs, rhs)| {
                assert_eq!(lhs.0, rhs.0);
                assert_eq!(lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(0..)
            .zip(btree.iter())
            .for_each(|(lhs, rhs)| {
                assert_eq!(lhs.0, rhs.0);
                assert_eq!(lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(0..10)
            .zip(btree.iter())
            .for_each(|(lhs, rhs)| {
                assert_eq!(lhs.0, rhs.0);
                assert_eq!(lhs.1, rhs.1);
            });
        let first_to_second: Vec<(usize, usize)> = (1..2).map(|x| (x, x)).collect();
        let three_til_end: Vec<(usize, usize)> = (3..10).map(|x| (x, x)).collect();
        let start_til_four: Vec<(usize, usize)> = (0..4).map(|x| (x, x)).collect();
        let start_til_end: Vec<(usize, usize)> = (0..10).map(|x| (x, x)).collect();
        let five_til_six_included: Vec<(usize, usize)> = (5..=6).map(|x| (x, x)).collect();
        let start_til_seven_included: Vec<(usize, usize)> = (0..=7).map(|x| (x, x)).collect();
        btree
            .clone()
            .range_mut_idx(1..2)
            .zip(first_to_second)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(3..10)
            .zip(three_til_end)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(0..4)
            .zip(start_til_four)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(0..10)
            .zip(start_til_end)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(5..=6)
            .zip(five_til_six_included)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
        btree
            .clone()
            .range_mut_idx(0..=7)
            .zip(start_til_seven_included)
            .for_each(|(lhs, rhs)| {
                assert_eq!(*lhs.0, rhs.0);
                assert_eq!(*lhs.1, rhs.1);
            });
    }

    #[test]
    fn test_non_boolean_set_operations() {
        let left_spine = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE + 1)).into_iter());
        let right_spine = BTreeSet::from_iter(
            ((DEFAULT_INNER_SIZE - 1)..((DEFAULT_INNER_SIZE + 1) * 2)).into_iter(),
        );

        let mut union = left_spine.clone();
        let mut temp_right_spine = right_spine.clone();
        union.append(&mut temp_right_spine);

        assert_eq!(
            Vec::from_iter(union.iter().cloned()),
            Vec::from_iter(left_spine.union(&right_spine).cloned())
        );
        assert_eq!(
            Vec::from_iter(union.iter().cloned()),
            Vec::from_iter(right_spine.union(&left_spine).cloned()),
        );

        let left_diff = Vec::from_iter(0..(DEFAULT_INNER_SIZE - 1));
        let right_diff = Vec::from_iter((DEFAULT_INNER_SIZE + 1)..((DEFAULT_INNER_SIZE + 1) * 2));

        assert_eq!(
            left_diff,
            Vec::from_iter(left_spine.difference(&right_spine).cloned())
        );
        assert_eq!(
            right_diff,
            Vec::from_iter(right_spine.difference(&left_spine).cloned())
        );

        let intersection = vec![DEFAULT_INNER_SIZE - 1, DEFAULT_INNER_SIZE];
        assert_eq!(
            intersection,
            Vec::from_iter(left_spine.intersection(&right_spine).cloned())
        );

        let mut sym_diff = left_diff.clone();
        sym_diff.append(&mut right_diff.clone());
        assert_eq!(
            sym_diff,
            Vec::from_iter(left_spine.symmetric_difference(&right_spine).cloned())
        );
        assert_eq!(
            sym_diff,
            Vec::from_iter(right_spine.symmetric_difference(&left_spine).cloned())
        );
    }

    #[test]
    fn test_boolean_set_operations() {
        let empty_set: BTreeSet<usize> = BTreeSet::new();
        assert!(empty_set.is_empty());
        let a = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE + 1)).into_iter());
        let b = BTreeSet::from_iter((0..(DEFAULT_INNER_SIZE + 2)).into_iter());
        let c =
            BTreeSet::from_iter(((DEFAULT_INNER_SIZE + 2)..(DEFAULT_INNER_SIZE + 4)).into_iter());

        assert!(a.is_subset(&a));
        assert!(a.is_superset(&a));
        assert!(a.is_subset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
        assert!(c.is_disjoint(&a));
        assert!(c.is_disjoint(&b));
        assert!(!a.is_disjoint(&b));
        assert!(!b.is_disjoint(&a));
    }

    #[test]
    fn test_split_off() {
        let btree: BTreeSet<usize> = BTreeSet::from_iter(0..(DEFAULT_INNER_SIZE * 10));
        for split in vec![
            1,
            (DEFAULT_INNER_SIZE * 3) - 6,
            DEFAULT_INNER_SIZE,
            DEFAULT_INNER_SIZE + 1,
            (DEFAULT_INNER_SIZE * 10) - 1,
        ] {
            let mut left = btree.clone();
            let right = left.split_off(&split);
            assert!(left.is_disjoint(&right));
            assert!(Vec::from_iter(left.intersection(&right)).is_empty());
            let expected_left = Vec::from_iter(0..split);
            let expected_right = Vec::from_iter(split..(DEFAULT_INNER_SIZE * 10));

            assert_eq!(expected_left, Vec::from_iter(left));
            let actual_right = Vec::from_iter(right);
            assert_eq!(expected_right, actual_right)
        }
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
        assert_eq!(
            btree.range(0..DEFAULT_INNER_SIZE).count(),
            (0..DEFAULT_INNER_SIZE).count()
        );
        assert_eq!(
            btree.range(0..=DEFAULT_INNER_SIZE).count(),
            (0..=DEFAULT_INNER_SIZE).count()
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
    fn test_map() {
        let mut btree: BTreeMap<usize, usize> = BTreeMap::new();
        assert_eq!(btree.iter().count(), 0);
        assert_eq!(btree.iter_mut().count(), 0);

        btree.insert(123, 456);
        assert_eq!(btree.iter().count(), 1);
        assert_eq!(btree.iter_mut().count(), 1);

        btree.insert(7, 8);
        assert_eq!(btree.iter().count(), 2);
        assert_eq!(btree.iter_mut().count(), 2);
    }

    #[test]
    fn test_many_fuzzy_duplicates() {
        // The below seed reproduces a previous bug
        let mut rng = rand::rngs::StdRng::from_seed([41u8; 32]);
        let mut btree = BTreeSet::new();
        let n = 100_000;
        for _ in 0..n {
            let value: u64 = rng.random_range(1..10000);
            let lower: u64 = 1650;
            let len_before = btree.len();
            // Use max to increase the number of duplicates
            if btree.insert(value.max(lower)) {
                assert_eq!(btree.len(), len_before + 1)
            } else {
                assert_eq!(btree.len(), len_before);
            }
        }
        let expected = btree.iter().cloned().collect::<Vec<_>>();
        assert_eq!(expected.len(), btree.len());
        for (i, expected_item) in expected.iter().enumerate() {
            if let Some(item) = btree.get_index(i) {
                assert_eq!(expected_item, item, "mismatch on index {i}");
            } else {
                panic!("missing index {i}")
            }
        }
    }

    #[test]
    fn test_iter_mut_rev() {
        let mut map = BTreeMap::<i64, i64>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);

        let expected_forward = vec![(1, 10), (2, 20), (3, 30)];
        for (i, (k, v)) in map.iter_mut().enumerate() {
            assert_eq!(*k, expected_forward[i].0);
            assert_eq!(*v, expected_forward[i].1);
        }

        let expected_backward = vec![(3, 30), (2, 20), (1, 10)];
        for (i, (k, v)) in map.iter_mut().rev().enumerate() {
            assert_eq!(*k, expected_backward[i].0);
            assert_eq!(*v, expected_backward[i].1); 
        }
    }

    #[test] // this test pass with std::collection::BTreeMap
    fn test_indexset_btreemap_overflow_bug() {
        // This test reproduces the "attempt to subtract with overflow" panic
        // that occurs in indexset::BTreeMap::range_to_idx at line 2639
        
        let mut map = BTreeMap::new();
        
        // Insert the same keys as in the failing test
        map.insert(vec![1, 2, 3, 4], 1);
        map.insert(vec![1, 2, 3, 7], 2);
        map.insert(vec![1, 2, 4, 5], 3);
        let end_key = vec![1, 2, 3, 4];
        
        let mut range_iter = map.range(..end_key).rev();
        
        let result = range_iter.next();
        
        // In a working implementation, this should return None
        // since there are no keys before [1,2,3,4]
        assert!(result.is_none(), "Expected None when ranging before first key");
    }

    use std::collections::Bound;
    use std::ops::RangeBounds;

    pub struct RangeFromExcluding<'a, T> {
        pub(crate) from: &'a T,
    }

    impl<T> RangeBounds<T> for RangeFromExcluding<'_, T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Excluded(self.from)
        }

        fn end_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
    }

    #[test]
    fn test_range_from_excluding_bug() {
        let mut map = BTreeMap::new();
        map.insert(vec![1, 2, 3, 4], 1);
        map.insert(vec![1, 2, 3, 7], 2);
        map.insert(vec![1, 2, 4, 5], 3);

        // RangeFromExcluding with non-existing key [1,2,3,6]
        // Should return [1,2,3,7] but returns [1,2,4,5]
        let non_existing_key = vec![1, 2, 3, 6];
        let range = RangeFromExcluding { from: &non_existing_key };
        let result = map.range(range).next().unwrap();
        
        assert_eq!(result.0, &vec![1, 2, 3, 7], "RangeFromExcluding skips entries incorrectly");
        assert_eq!(*result.1, 2);
    }

    #[test]
    fn uuid_key_test() {
        let mut map = BTreeMap::new();

        map.insert(uuid::uuid!("019c34bf-47c0-7df1-9d46-522cec0dd95f"), 1);

        let out = map.get_mut(&uuid::uuid!("019c34bf-47c0-7df1-9d46-52013234139b"));
        assert!(out.is_none());
    }
}
