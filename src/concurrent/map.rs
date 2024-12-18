use std::{borrow::Borrow, iter::FusedIterator};

use crate::core::pair::Pair;

use super::set::BTreeSet;

#[derive(Debug)]
pub struct BTreeMap<K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    set: BTreeSet<Pair<K, V>>
}

impl<K: Send + Ord + Clone, V: Send + Clone + 'static> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self {
            set: Default::default(),
        }
    }
}

pub struct Iter<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    inner: super::set::Iter<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> FusedIterator for Iter<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
}

pub struct Range<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    inner: super::set::Range<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Range<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(entry) = self.inner.next_back() {
            return Some((&entry.key, &entry.value));
        }

        None
    }
}

impl<'a, K, V> FusedIterator for Range<'a, K, V>
where
    K: Send + Ord + Clone + 'static,
    V: Send + Clone + 'static,
{
}

impl<K: Send + Ord + Clone + 'static, V: Send + Clone + 'static> BTreeMap<K, V> {
    /// Makes a new, empty, persistent `BTreeMap`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(1, "a");
    /// ```
    pub fn new() -> Self {
        Self {
            set: Default::default(),
        }
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        self.set
            .contains(key)
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1).and_then(|e| Some(e.get().value)), Some("a"));
    /// assert_eq!(map.get(&2).and_then(|e| Some(e.get().value)), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<super::set::Ref<Pair<K, V>>>
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.len() == 0, false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map.get(&37).and_then(|e| Some(e.get().value)), Some("c"));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let new_entry = Pair { key, value };

        self.set.put(new_entry).and_then(|pair| Some(pair.value))
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some((1, "a")));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        return self
            .set
            .remove(key)
            .and_then(|pair| Some((pair.key, pair.value)))
    }
    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut a = BTreeMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.set.len()
    }
    /// Gets an iterator over the entries of the map, sorted by key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use indexset::concurrent::map::BTreeMap;
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
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            inner: self.set.iter(),
        }
    }
}