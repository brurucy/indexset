use std::{borrow::Borrow, iter::FusedIterator, ops::RangeBounds};
use std::fmt::Debug;
use std::sync::Arc;

use parking_lot::Mutex;

use crate::{cdc::change::ChangeEvent, core::multipair::MultiPair};
use crate::core::node::NodeLike;

use super::set::BTreeSet;

#[derive(Debug)]
pub struct BTreeMultiMap<K, V, Node = Vec<MultiPair<K, V>>>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    pub(crate) set: BTreeSet<MultiPair<K, V>, Node>,
}

impl<K, V, Node> Default for BTreeMultiMap<K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    fn default() -> Self {
        Self {
            set: Default::default(),
        }
    }
}

pub struct Iter<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    inner: super::set::Iter<'a, MultiPair<K, V>, Node>,
}

impl<'a, K, V, Node> Iterator for Iter<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{

    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> DoubleEndedIterator for Iter<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> FusedIterator for Iter<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{}

pub struct RawRange<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V: Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static

{
    inner: super::set::Range<'a, MultiPair<K, V>, Node>,
}

impl<'a, K, V, Node> Iterator for RawRange<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    type Item = (&'a K, &'a u64, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.discriminator, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> DoubleEndedIterator for RawRange<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.discriminator, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> FusedIterator for RawRange<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{}


pub struct Range<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    inner: RawRange<'a, K, V, Node>,
}

impl<'a, K, V, Node> Iterator for Range<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(raw_entry) = self.inner.next() {
            return Some((&raw_entry.0, &raw_entry.2));
        }

        None
    }
}

impl<'a, K, V, Node> DoubleEndedIterator for Range<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(raw_entry) = self.inner.next_back() {
            return Some((&raw_entry.0, &raw_entry.2));
        }

        None
    }
}

impl<'a, K, V, Node> FusedIterator for Range<'a, K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
}

impl<K, V, Node> BTreeMultiMap<K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V:  Debug + Send + Clone + PartialEq + 'static,
      Node: NodeLike<MultiPair<K, V>> + Send + 'static
{
    /// Makes a new, empty, persistent `BTreeMultiMap`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new() -> Self {
        Self {
            set: Default::default(),
        }
    }
    /// Makes a new, empty `BTreeMultiMap` with the given maximum node size. Allocates one vec with
    /// the capacity set to be the specified node size.
    ///
    /// # Examples
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let map = BTreeMultiMap::<i32, i32>::with_maximum_node_size(128);
    pub fn with_maximum_node_size(node_capacity: usize) -> Self {
        Self {
            set: BTreeSet::with_maximum_node_size(node_capacity),
        }
    }
    /// Adds full [`Node`] to this multiset. [`Node`] should be correct node with
    /// values sorted.
    #[cfg(feature = "cdc")]
    pub fn attach_multi_node(&self, node: Node) {
        self.set.attach_node(node)
    }
    /// Returns iterator over this multiset's [`Node`]'s.
    #[cfg(feature = "cdc")]
    pub fn iter_nodes(&self) -> impl Iterator<Item=Arc<Mutex<Node>>> + '_ {
        self.set.index.iter().map(|e| e.value().clone())
    }
    /// Returns `true` if the map contains at least one occurance of the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
    /// map.insert(1, "a");
    /// map.insert(1, "b");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        MultiPair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.set.contains(key)
    }
    fn _range<Q, R>(&self, range: R) -> Range<K, V,Node>
    where
        MultiPair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        Range {
            inner: RawRange {
                inner: super::set::BTreeSet::range(&self.set, range),
            },
        }
    }
    fn raw_get(&self, key: &K) -> RawRange<K, V, Node> {
        let infimum = MultiPair::with_infimum(key.clone());
        let supremum = MultiPair::with_supremum(key.clone());

        RawRange {
            inner: self.set.range(infimum..supremum),
        }
    }
    /// Constructs a double-ended iterator over all key value pairs with the given key in the map.
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    /// use wt_indexset::BTreeSet;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
    ///
    /// map.insert(1, "b");
    /// map.insert(1, "a");
    /// map.insert(2, "c");
    ///
    /// let all_with_key = map.get(&1).collect::<BTreeSet<_>>();
    /// assert_eq!(all_with_key.len(), 2);
    /// assert_eq!(all_with_key, vec![(&1, &"a"), (&1, &"b")].into_iter().collect::<BTreeSet<_>>());
    /// ```
    pub fn get(&self, key: &K) -> Range<K, V, Node>
    {
        let infimum = MultiPair::with_infimum(key.clone());
        let supremum = MultiPair::with_supremum(key.clone());

        Range {
            inner: RawRange {
                inner: self.set.range(infimum..supremum),
            },
        }
    }
    /// Inserts a key-value pair into the multi map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.len() == 0, false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), None);
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let new_entry = MultiPair::new(key, value);

        self.set
            .put_cdc(new_entry)
            .0
            .and_then(|pair| Some(pair.value))
    }
    /// Inserts a key-value pair into the map and returns old value (if it was
    /// already in set) with [`ChangeEvent`]'s that describes this insert
    /// action.
    #[cfg(feature = "cdc")]
    pub fn insert_cdc(&self, key: K, value: V) -> (Option<V>, Vec<ChangeEvent<MultiPair<K, V>>>) {
        let new_entry = MultiPair::new(key, value);

        let (old_value, cdc) = self.set.put_cdc(new_entry);

        (old_value.and_then(|pair| Some(pair.value)), cdc)
    }
    /// Removes some key from the map that matches the given key, returning the
    /// key and the value if the key was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let map = BTreeMultiMap::<usize, &str>::new();
    /// map.insert(1, "b");
    /// map.insert(1, "a");
    ///
    /// let first_removed = map.remove_some(&1).unwrap();
    /// let second_removed = map.remove_some(&1).unwrap();
    /// let removals = vec![first_removed, second_removed];
    ///
    /// assert!(removals.contains(&(1, "a")));
    /// assert!(removals.contains(&(1, "b")));
    /// ```
    pub fn remove_some<Q>(&self, key: &Q) -> Option<(K, V)>
    where
        MultiPair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self
            .set
            .remove(key)
            .and_then(|pair| Some((pair.key, pair.value)))
    }
    /// Removes some key from the map that matches the given key, returning the
    /// key and the value if the key was previously in the map with
    /// [`ChangeEvent`]'s describing this `remove_some` action.
    #[cfg(feature = "cdc")]
    pub fn remove_some_cdc<Q>(&self, key: &Q) -> (Option<(K, V)>, Vec<ChangeEvent<MultiPair<K, V>>>)
    where
        MultiPair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (old_value, cdc) = self.set.remove_cdc(key);

        (old_value.and_then(|pair| Some((pair.key, pair.value))), cdc)
    }
    /// Removes a specific key-value pair from the map returning the key and the value if the key
    /// was previously in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let map = BTreeMultiMap::<usize, &str>::new();
    /// map.insert(1, "b");
    /// map.insert(1, "a");
    ///
    /// assert_eq!(map.remove(&1, &"a"), Some((1, "a")));
    /// assert_eq!(map.remove(&1, &"b"), Some((1, "b")));
    /// ```
    pub fn remove(&self, key: &K, value: &V) -> Option<(K, V)>
    {
        let discriminant_to_remove = self.raw_get(&key).find(|pair| pair.2 == value);
        if let Some(discriminant_to_remove) = discriminant_to_remove {
            let pair_to_remove = MultiPair { key: discriminant_to_remove.0.clone(), value: discriminant_to_remove.2.clone(), discriminator: *discriminant_to_remove.1 };

            return self.set.remove(&pair_to_remove).and_then(|pair| Some((pair.key, pair.value)));
        }

        None
    }
    /// Removes a specific key-value pair from the map returning the key and the
    /// value if the key was previously in the map with [`ChangeEvent`]'s
    /// describing this `remove_some` action.
    #[cfg(feature = "cdc")]
    pub fn remove_cdc(&self, key: &K, value: &V) -> (Option<(K, V)>, Vec<ChangeEvent<MultiPair<K, V>>>)
    {
        let discriminant_to_remove = self.raw_get(&key).find(|pair| pair.2 == value);
        if let Some(discriminant_to_remove) = discriminant_to_remove {
            let pair_to_remove = MultiPair { key: discriminant_to_remove.0.clone(), value: discriminant_to_remove.2.clone(), discriminator: *discriminant_to_remove.1 };

            let (res, evs) = self.set.remove_cdc(&pair_to_remove);
            return (res.map(|pair| (pair.key, pair.value)), evs)
        }

        (None, vec![])
    }
    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut a = BTreeMultiMap::<usize, &str>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.set.len()
    }
    /// Returns the total number of allocated slots across all internal nodes.
    ///
    /// This represents the number of key-value pairs the multimap can hold
    /// without reallocating memory in its internal vectors.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut a = BTreeMultiMap::<usize, &str>::with_maximum_node_size(8);
    ///
    /// a.insert(1, "a");
    /// a.insert(1, "b");
    ///
    /// // Capacity remains unchanged until reallocation occurs
    /// assert_eq!(a.capacity(), 8);
    /// ```
    pub fn capacity(&self) -> usize {
        self.set.capacity()
    }
    /// Returns the total number of nodes.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut a = BTreeMap::<usize, &str>::with_maximum_node_size(16);
    ///
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// assert_eq!(a.node_count(), 1);
    /// ```
    pub fn node_count(&self) -> usize {
        self.set.node_count()
    }
    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
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
    pub fn iter(&self) -> Iter<K, V, Node> {
        Iter {
            inner: self.set.iter(),
        }
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
    /// use wt_indexset::concurrent::multimap::BTreeMultiMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = BTreeMultiMap::<usize, &str>::new();
    /// map.insert(3, "a");
    /// map.insert(5, "b");
    /// map.insert(8, "c");
    /// for (&key, &value) in map.range((Included(&4), Included(&8))) {
    ///     println!("{key}: {value}");
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(4..).next());
    /// ```
    pub fn range<R>(&self, range: R) -> Range<K, V, Node>
    where
        R: RangeBounds<K>,
    {
        let start_bound = range.start_bound();
        let adjusted_start_bound = match start_bound {
            std::ops::Bound::Included(start) => std::ops::Bound::Included(MultiPair::with_infimum(start.clone())),
            std::ops::Bound::Excluded(start) => std::ops::Bound::Excluded(MultiPair::with_supremum(start.clone())),
            _ => std::ops::Bound::Unbounded,
        };
        let end_bound = range.end_bound();
        let adjusted_end_bound = match end_bound {
            std::ops::Bound::Included(end) => std::ops::Bound::Included(MultiPair::with_supremum(end.clone())),
            std::ops::Bound::Excluded(end) => std::ops::Bound::Excluded(MultiPair::with_infimum(end.clone())),
            _ => std::ops::Bound::Unbounded,
        };

        self._range((adjusted_start_bound, adjusted_end_bound))
    }
}

#[cfg(test)]
mod tests {
    use super::BTreeMultiMap;
    use crate::BTreeSet;

    #[test]
    fn test_insert_works_as_expected() {
        let maximum_node_size = 3;
        let multi_map = BTreeMultiMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        multi_map.insert(1usize, "a");
        multi_map.insert(1usize, "b");
        multi_map.insert(2usize, "c");
        multi_map.insert(2usize, "d");
        multi_map.insert(3usize, "e");
        multi_map.insert(4usize, "f");
        multi_map.insert(4usize, "g");

        let expected_pairs = vec![
            (&1, &"b"),
            (&1, &"a"),
            (&2, &"d"),
            (&2, &"c"),
            (&3, &"e"),
            (&4, &"f"),
            (&4, &"g"),
        ]
            .into_iter()
            .collect::<BTreeSet<_>>();

        let all_pairs = multi_map.iter().collect::<BTreeSet<_>>();
        assert_eq!(all_pairs, expected_pairs);
    }

    #[test]
    fn test_insert_all_same_key_works_as_expected() {
        let maximum_node_size = 3;
        let map = BTreeMultiMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        map.insert(1usize, "a");
        map.insert(1usize, "b");
        map.insert(1usize, "c");
        map.insert(1usize, "d");
        map.insert(1usize, "e");
        map.insert(1usize, "f");

        let all_actual_pairs = map.iter().map(|(k, v)| (*k, *v)).collect::<BTreeSet<_>>();
        let all_expected_pairs = vec![(1, "f"), (1, "e"), (1, "d"), (1, "c"), (1, "b"), (1, "a")]
            .into_iter()
            .collect::<BTreeSet<_>>();
        assert_eq!(all_actual_pairs, all_expected_pairs);
    }

    #[test]
    fn test_range_edge_cast() {
        let maximum_node_size = 3;
        let map = BTreeMultiMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        map.insert(1usize, "a");
        map.insert(1usize, "b");
        map.insert(2usize, "c");
        map.insert(2usize, "d");
        map.insert(3usize, "e");
        map.insert(4usize, "f");
        map.insert(4usize, "g");

        let mid_range = map.range(2..3).collect::<BTreeSet<_>>();
        assert_eq!(mid_range, vec![
            (&2, &"c"),
            (&2, &"d"),
        ].into_iter().collect::<BTreeSet<_>>());
    }


    #[test]
    fn test_range_works_as_expected() {
        let maximum_node_size = 3;
        let map = BTreeMultiMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        map.insert(1usize, "a");
        map.insert(1usize, "b");
        map.insert(2usize, "c");
        map.insert(2usize, "d");
        map.insert(3usize, "e");
        map.insert(4usize, "f");
        map.insert(4usize, "g");

        let truly_all_pairs = map.iter().collect::<BTreeSet<_>>();
        let all_pairs = map.range(..).collect::<BTreeSet<_>>();
        assert_eq!(all_pairs, truly_all_pairs);

        let mid_range = map.range(2..3).collect::<BTreeSet<_>>();
        assert_eq!(mid_range, vec![
            (&2, &"c"),
            (&2, &"d"),
        ].into_iter().collect::<BTreeSet<_>>());

        let reverse_range = map.range(1..4).rev().collect::<BTreeSet<_>>();
        assert_eq!(reverse_range, vec![
            (&3, &"e"),
            (&2, &"d"),
            (&2, &"c"),
            (&1, &"b"),
            (&1, &"a"),
        ].into_iter().collect::<BTreeSet<_>>());

        let empty_range = map.range(5..).collect::<BTreeSet<_>>();
        assert_eq!(empty_range, vec![].into_iter().collect::<BTreeSet<_>>());
    }

    #[test]
    fn test_get_works_as_expected() {
        let maximum_node_size = 10;
        let map = BTreeMultiMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        map.insert(1usize, "a");
        map.insert(1usize, "b");
        map.insert(2usize, "c");
        map.insert(2usize, "d");
        map.insert(3usize, "e");
        map.insert(4usize, "f");
        map.insert(4usize, "g");

        let range = map.get(&1).collect::<BTreeSet<_>>();

        assert_eq!(range, vec![
            (&1, &"b"),
            (&1, &"a"),
        ].into_iter().collect::<BTreeSet<_>>());

        let range = map.get(&2).collect::<BTreeSet<_>>();
        assert_eq!(range, vec![
            (&2, &"d"),
            (&2, &"c"),
        ].into_iter().collect::<BTreeSet<_>>());

        let range = map.get(&3).collect::<BTreeSet<_>>();
        assert_eq!(range, vec![
            (&3, &"e"),
        ].into_iter().collect::<BTreeSet<_>>());

        let range = map.get(&4).collect::<BTreeSet<_>>();
        assert_eq!(range, vec![
            (&4, &"g"),
            (&4, &"f"),
        ].into_iter().collect::<BTreeSet<_>>());
    }

    #[test]
    fn test_get_works_as_expected_at_big_amounts() {
        let maximum_node_size = 100;
        let map = BTreeMultiMap::<String, usize>::with_maximum_node_size(maximum_node_size);

        for i in 1..2000 {
            map.insert(format!("ValueNum{}", i), i);
        }

        for i in 1..2000 {
            let range = map.get(&format!("ValueNum{}", i)).collect::<BTreeSet<_>>();
            assert_eq!(range, vec![
                (&format!("ValueNum{}", i), &i),
            ].into_iter().collect::<BTreeSet<_>>());
        }
    }
}
