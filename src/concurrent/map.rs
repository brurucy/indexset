use std::{borrow::Borrow, iter::FusedIterator, ops::RangeBounds};
use std::fmt::Debug;
use std::sync::Arc;

use parking_lot::Mutex;

use crate::{cdc::change::ChangeEvent, core::pair::Pair};
use crate::core::node::NodeLike;
use super::set::BTreeSet;

#[derive(Debug)]
pub struct BTreeMap<K, V, Node = Vec<Pair<K, V>>>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>>
{
    pub(crate) set: BTreeSet<Pair<K, V>, Node>,
}

impl<K, V, Node> Default for BTreeMap<K, V, Node>
where K: Send + Ord + Clone,
      V: Send + Clone + 'static,
      Node: NodeLike<Pair<K, V>> + Send + 'static
{
    fn default() -> Self {
        Self {
            set: Default::default(),
        }
    }
}

pub struct Iter<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
    inner: super::set::Iter<'a, Pair<K, V>, Node>,
}

impl<'a, K, V, Node> Iterator for Iter<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
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
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> FusedIterator for Iter<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
}

pub struct Range<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
    inner: super::set::Range<'a, Pair<K, V>, Node>,
}

impl<'a, K, V, Node> Iterator for Range<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> DoubleEndedIterator for Range<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V, Node> FusedIterator for Range<'a, K, V, Node>
where
    K: Debug + Send + Ord + Clone + 'static,
    V: Debug + Send + Clone + 'static,
    Node: NodeLike<Pair<K, V>> + Send + 'static
{
}

impl<K, V, Node> BTreeMap<K, V, Node>
where K: Debug + Send + Ord + Clone + 'static,
      V: Debug + Send + Clone + 'static,
      Node: NodeLike<Pair<K, V>> + Send + 'static
{
    /// Makes a new, empty, persistent `BTreeMap`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::<usize, &str>::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new() -> Self {
        Self {
            set: Default::default(),
        }
    }
    /// Makes a new, empty `BTreeMap` with the given maximum node size. Allocates one vec with
    /// the capacity set to be the specified node size.
    ///
    /// # Examples
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let map = BTreeMap::<i32, i32>::with_maximum_node_size(128);
    pub fn with_maximum_node_size(node_capacity: usize) -> Self {
        Self {
            set: BTreeSet::with_maximum_node_size(node_capacity),
        }
    }
    /// Adds full [`Node`] to this set. [`Node`] should be correct node with
    /// values sorted.
    #[cfg(feature = "cdc")]
    pub fn attach_node(&self, node: Node) {
        self.set.attach_node(node)
    }
    /// Returns iterator over this set's [`Node`]'s.
    #[cfg(feature = "cdc")]
    pub fn iter_nodes(&self) -> impl Iterator<Item=Arc<Mutex<Node>>> + '_ {
        self.set.index.iter().map(|e| e.value().clone())
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
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::<usize, &str>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.set.contains(key)
    }
    /// Returns a reference to a pair whose key corresponds to the input.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::<usize, &str>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1).and_then(|e| Some(e.get().value)), Some("a"));
    /// assert_eq!(map.get(&2).and_then(|e| Some(e.get().value)), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<super::r#ref::Ref<Pair<K, V>, Node>>
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.set.get(key)
    }
    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, it will be inserted.
    ///
    /// Otherwise, the value is updated.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::<usize, &str>::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.len() == 0, false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map.get(&37).and_then(|e| Some(e.get().value)), Some("c"));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let new_entry = Pair { key, value };

        self.set
            .put_cdc(new_entry)
            .0
            .and_then(|pair| Some(pair.value))
    }
    pub fn checked_insert(&self, key: K, value: V) -> Option<()> {
        let new_entry = Pair { key, value };
        self.set.put_cdc_checked(new_entry).ok().map(|_| ())
    }
    /// Inserts a key-value pair into the map and returns old value (if it was
    /// already in set) with [`ChangeEvent`]'s that describes this insert
    /// action.
    pub fn insert_cdc(&self, key: K, value: V) -> (Option<V>, Vec<ChangeEvent<Pair<K, V>>>) {
        let new_entry = Pair { key, value };

        let (old_value, cdc) = self.set.put_cdc(new_entry);

        (old_value.and_then(|pair| Some(pair.value)), cdc)
    }
    pub fn checked_insert_cdc(&self, key: K, value: V) -> Option<Vec<ChangeEvent<Pair<K, V>>>> {
        let new_entry = Pair { key, value };
        self.set.put_cdc_checked(new_entry).ok().map(|(_, evs)| evs)
    }
    /// Removes a key from the map, returning the key and the value if the key
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
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let map = BTreeMap::<usize, &str>::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&self, key: &Q) -> Option<(K, V)>
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self
            .set
            .remove(key)
            .and_then(|pair| Some((pair.key, pair.value)))
    }
    /// Removes a key from the map, returning the key and the value if the key
    /// was previously in the map and [`ChangeEvent`]s describing changes caused
    /// by this action.
    pub fn remove_cdc<Q>(&self, key: &Q) -> (Option<(K, V)>, Vec<ChangeEvent<Pair<K, V>>>)
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        let (old_value, cdc) = self.set.remove_cdc(key);

        (old_value.and_then(|pair| Some((pair.key, pair.value))), cdc)
    }
    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut a = BTreeMap::<usize, &str>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.set.len()
    }
    /// Returns the total number of allocated slots across all internal nodes.
    ///
    /// This represents the number of key-value pairs the map can hold
    /// without reallocating memory in its internal vectors.
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
    /// // Capacity remains the same until node is split or reallocated
    /// assert_eq!(a.capacity(), 16);
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
    /// use wt_indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::<usize, &str>::new();
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
    /// use wt_indexset::concurrent::map::BTreeMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = BTreeMap::<i32, &str>::new();
    /// map.insert(3, "a");
    /// map.insert(5, "b");
    /// map.insert(8, "c");
    /// for (&key, &value) in map.range::<i32, _>((Included(&4), Included(&8))) {
    ///     println!("{key}: {value}");
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(4..).next());
    /// ```
    pub fn range<Q, R>(&self, range: R) -> Range<K, V, Node>
    where
        Pair<K, V>: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        Range {
            inner: BTreeSet::range(&self.set, range),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use std::sync::{Arc, Mutex};
    use std::thread;
    use rand::Rng;
    use scc::HashMap;
    use crate::BTreeSet;
    use super::BTreeMap;
    use super::ChangeEvent;
    use super::Pair;

    #[test]
    fn test_range_edge_cast() {
        let maximum_node_size = 3;
        let map = BTreeMap::<usize, &str>::with_maximum_node_size(maximum_node_size);

        map.insert(1usize, "a");

        map.insert(2usize, "b");
        map.insert(3usize, "c");

        map.insert(4usize, "d");
        map.insert(5usize, "e");

        map.insert(6usize, "f");
        map.insert(7usize, "g");

        let mid_range = map.range::<usize, _>(3..5).collect::<BTreeSet<_>>();
        assert_eq!(mid_range, vec![
            (&3usize, &"c"),
            (&4usize, &"d"),
        ].into_iter().collect::<BTreeSet<_>>());
    }

    #[derive(Debug, Default)]
    struct PersistedBTreeMap<K, V>
    where
        K: Debug + Ord + Clone,
        V: Debug + Clone + PartialEq,
    {
        nodes: std::collections::BTreeMap<K, Vec<Pair<K, V>>>,
    }

    impl<K: Debug + Ord + Clone, V: Debug + Clone + PartialEq> PersistedBTreeMap<K, V> {
        fn persist(&mut self, event: &ChangeEvent<Pair<K, V>>) {
            match event {
                ChangeEvent::CreateNode { max_value, event_id: _ } => {
                    let node = vec![max_value.clone()];
                    self.nodes.insert(max_value.key.clone(), node);
                }
                ChangeEvent::RemoveNode { max_value, event_id: _   } => {
                    self.nodes.remove(&max_value.key);
                }
                ChangeEvent::InsertAt {
                    max_value,
                    index,
                    value,
                    event_id: _,
                } => {
                    if let Some(node) = self.nodes.get_mut(&max_value.key) {
                        node.insert(*index, value.clone());
                    }
                    if max_value.key < value.key {
                        let node = self.nodes.remove(&max_value.key).unwrap();
                        self.nodes.insert(value.key.clone(), node);
                    }
                }
                ChangeEvent::RemoveAt {
                    max_value,
                    index,
                    value: _, event_id: _
                } => {
                    if let Some(node) = self.nodes.get_mut(&max_value.key) {
                        node.remove(*index);
                    }
                }
                ChangeEvent::SplitNode {
                    max_value,
                    split_index, event_id: _
                } => {
                    if let Some(mut old_node) = self.nodes.remove(&max_value.key) {
                        let new_node = old_node.split_off(*split_index);
                        let new_max_value = new_node.last().unwrap();
                        self.nodes.insert(new_max_value.key.clone(), new_node);
                        let old_max_value = old_node.last().unwrap();
                        self.nodes.insert(old_max_value.key.clone(), old_node);
                    }
                }
            }
        }

        fn contains_pair(&self, key: &K, value: &V) -> bool {
            for node in self.nodes.values() {
                if let Ok(pos) = node.binary_search(&Pair {
                    key: key.clone(),
                    value: value.clone(),
                }) {
                    if node[pos].value == *value {
                        return true;
                    }
                }
            }
            false
        }
    }

    #[cfg(feature = "cdc")]
    #[test]
    fn test_cdc_single_insert() {
        let map = BTreeMap::<usize, &str>::new();
        let mut mock_state = PersistedBTreeMap::default();

        let (_, events) = map.insert_cdc(1, "a");

        for event in events {
            mock_state.persist(&event);
        }

        assert!(mock_state.contains_pair(&1, &"a"));
        assert!(map.contains_key(&1));
        assert_eq!(map.get(&1).unwrap().get().value, "a");

        let expected_state = map
            .set
            .index
            .iter()
            .map(|e| (e.key().clone().key, e.value().lock_arc().clone()))
            .collect::<_>();
        assert_eq!(mock_state.nodes, expected_state);
    }

    #[cfg(feature = "cdc")]
    #[test]
    fn test_cdc_multiple_inserts() {
        let map = BTreeMap::<usize, String>::new();
        let mut mock_state = PersistedBTreeMap::default();

        for i in 0..1024 {
            let (_, events) = map.insert_cdc(i, format!("val{}", i));

            for event in events {
                mock_state.persist(&event);
            }
        }

        for i in 0..1024 {
            assert!(mock_state.contains_pair(&i, &format!("val{}", i)));
            assert!(map.contains_key(&i));
            assert_eq!(map.get(&i).unwrap().get().value, format!("val{}", i));
        }

        let expected_state = map
            .set
            .index
            .iter()
            .map(|e| (e.key().clone().key, e.value().lock_arc().clone()))
            .collect::<_>();
        assert_eq!(mock_state.nodes, expected_state);
    }

    #[cfg(feature = "cdc")]
    #[test]
    fn test_cdc_updates() {
        let map = BTreeMap::<usize, &str>::new();
        let mut mock_state = PersistedBTreeMap::default();

        let (_, events) = map.insert_cdc(1, "a");
        for event in events {
            mock_state.persist(&event);
        }

        let (_, events) = map.insert_cdc(1, "b");
        for event in events {
            mock_state.persist(&event);
        }

        assert!(mock_state.contains_pair(&1, &"b"));
        assert!(!mock_state.contains_pair(&1, &"a"));
        assert!(map.contains_key(&1));
        assert_eq!(map.get(&1).unwrap().get().value, "b");

        let expected_state = map
            .set
            .index
            .iter()
            .map(|e| (e.key().clone().key, e.value().lock_arc().clone()))
            .collect::<_>();
        assert_eq!(mock_state.nodes, expected_state);
    }

    #[cfg(feature = "cdc")]
    #[test]
    fn test_cdc_node_splits() {
        let map = BTreeMap::<usize, String>::new();
        let mut mock_state = PersistedBTreeMap::default();

        let n = crate::core::constants::DEFAULT_INNER_SIZE + 10;

        for i in 0..n {
            let (_, events) = map.insert_cdc(i, format!("val{}", i));
            for event in events {
                mock_state.persist(&event);
            }
        }

        for i in 0..n {
            assert!(mock_state.contains_pair(&i, &format!("val{}", i)));
            assert!(map.contains_key(&i));
            assert_eq!(map.get(&i).unwrap().get().value, format!("val{}", i));
        }

        assert!(mock_state.nodes.len() > 1);

        let expected_state = map
            .set
            .index
            .iter()
            .map(|e| (e.key().clone().key, e.value().lock_arc().clone()))
            .collect::<_>();
        assert_eq!(mock_state.nodes, expected_state);
    }

    #[cfg(feature = "cdc")]
    #[test]
    fn test_concurrent_insert_cdc() {
        let map = Arc::new(BTreeMap::<usize, String>::new());
        let num_threads = 8;
        let operations_per_thread = 1000;
        let mut handles = vec![];

        let test_data: Vec<Vec<(i32, (usize, String))>> = (0..num_threads)
            .map(|_| {
                let mut rng = rand::rng();
                (0..operations_per_thread)
                    .map(|_| {
                        let value = rng.random_range(0..100000);
                        let operation = rng.random_range(0..2);
                        (operation, (value, format!("val{value}")))
                    })
                    .collect()
            })
            .collect();

        let expected_values = Arc::new(Mutex::new(HashMap::new()));

        for thread_idx in 0..num_threads {
            let map_clone = Arc::clone(&map);
            let expected_values = Arc::clone(&expected_values);
            let thread_data = test_data[thread_idx].clone();

            let handle = thread::spawn(move || {
                let mut events = Vec::new();
                for (operation, (k, v)) in thread_data {
                    if operation == 0 {
                        let (_, evs) = map_clone.insert_cdc(k, v.clone());
                        events.extend(evs);
                        let _ = expected_values.lock().unwrap().insert(k, v);
                    }
                }
                events
            });
            handles.push(handle);
        }

        let mut final_events = Vec::new();
        for handle in handles {
            let thread_events = handle.join().unwrap();
            final_events.extend(thread_events)
        }
        final_events.sort_by(|ev1, ev2| ev1.id().cmp(&ev2.id()));


        let mut mock_state = PersistedBTreeMap::default();
        for ev in final_events {
            mock_state.persist(&ev);
        }

        // let expected_values = expected_values.lock().unwrap();
        // assert_eq!(mock_state.len(), expected_values.len());

        let expected_state = map
            .set
            .index
            .iter()
            .map(|e| (e.key().clone().key, e.value().lock_arc().clone()))
            .collect::<_>();
        assert_eq!(mock_state.nodes, expected_state);
    }
}
