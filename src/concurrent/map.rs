use crate::concurrent::set;
use crate::core::pair::Pair;
use std::borrow::Borrow;
use std::iter::FusedIterator;
use std::ops::RangeBounds;

/// A persistent and concurrent ordered map based on a two-level [B-Tree].
///
/// See the documentation on the non-concurrent version for an understanding of how this crate's B-Tree implementation differs from
/// the one in the standard library.
///
///
/// # Examples
///
/// ```
/// use indexset::concurrent::map::BTreeMap;
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
/// if !movie_reviews.contains_key(&"Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              movie_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// movie_reviews.remove(&"The Blues Brothers");
///
/// // look up the values associated with some keys.
/// let to_find = ["Up!", "Office Space"];
/// for movie in &to_find {
///     movie_reviews.get(movie, |review| println!("{movie}: {review}"));
/// }
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
/// use indexset::concurrent::map::BTreeMap;
///
/// let solar_distance = BTreeMap::from_iter([
///     ("Mercury", 0.4),
///     ("Venus", 0.7),
///     ("Earth", 1.0),
///     ("Mars", 1.5),
/// ]);
/// ```
pub struct BTreeMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    set: set::BTreeSet<Pair<K, V>>,
}

impl<K: Ord + Clone, V: Clone> Default for BTreeMap<K, V> {
    fn default() -> Self {
        Self {
            set: Default::default(),
        }
    }
}

pub struct Iter<'a, K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    inner: set::Iter<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Ord + Clone,
    V: Clone,
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
    K: Ord + Clone,
    V: Clone,
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
    K: Ord + Clone,
    V: Clone,
{
}

pub struct Range<'a, K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    inner: set::Range<'a, Pair<K, V>>,
}

impl<'a, K, V> Iterator for Range<'a, K, V>
where
    K: Ord + Clone,
    V: Clone,
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
    K: Ord + Clone,
    V: Clone,
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
    K: Ord + Clone,
    V: Clone,
{
}

impl<K: Ord + Clone, V: Clone> BTreeMap<K, V> {
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
            .contains_cmp(|item| item.borrow() < key, |item| item.borrow() == key)
    }

    pub fn get<Q, F>(&self, key: &Q, mut f: F)
    where
        Pair<K, V>: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
        F: FnMut(&V),
    {
        self.set.get(
            |item| item.borrow() < key,
            |item| item.borrow() == key,
            |pair| f(&pair.value),
        )
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.len() == 0, false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// map.get(&37, |value| assert_eq!(value, &"c"));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        if self.contains_key(&key) {
            let new_entry = Pair { key, value };

            //let old_entry = self.set.delete(&new_entry).1?.value;

            self.set.insert(new_entry);

            //Some(old_entry)
            None
        } else {
            self.set.insert(Pair { key, value });

            None
        }
    }
    /// Adds a value to the set, under the assumption that the current thread is the only one
    /// that is currently inserting (no problems with readers though). Super unsafe, stay clear
    /// unless you know what you are doing.
    pub fn insert_spmc(&self, key: K, value: V) -> Option<V> {
        if self.contains_key(&key) {
            let new_entry = Pair { key, value };

            //let old_entry = self.set.delete(&new_entry).1?.value;

            self.set.insert_spmc(new_entry);

            //Some(old_entry)
            None
        } else {
            self.set.insert_spmc(Pair { key, value });

            None
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
    /// use indexset::concurrent::map::BTreeMap;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    // pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    // where
    //     Pair<K, V>: Borrow<Q> + Ord,
    //     Q: Ord + ?Sized,
    // {
    //     let (removed, old_entry) = self
    //         .set
    //         .delete_cmp(|x| x.borrow() < key, |x| x.borrow() == key);

    //     if removed {
    //         return Some(old_entry?.value);
    //     }

    //     None
    // }
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
    /// use indexset::concurrent::map::BTreeMap;
    /// use std::ops::Bound::Included;
    ///
    /// let mut map = BTreeMap::new();
    /// map.insert(3, "a");
    /// map.insert(5, "b");
    /// map.insert(8, "c");
    /// for (key, value) in map.range((Included(4), Included(8))) {
    ///     println!("{key}: {value}");
    /// }
    /// assert_eq!(Some((&5, &"b")), map.range(4..).next());
    /// ```
    pub fn range<R, Q>(&self, range: R) -> Range<'_, K, V>
    where
        Q: Ord + ?Sized,
        Pair<K, V>: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        Range {
            inner: self.set.range(range),
        }
    }
    pub fn remove_range<R, Q>(&self, range: R)
    where
        Q: Ord + ?Sized,
        Pair<K, V>: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        self.set.remove_range(range)
    }
}

impl<K, V> FromIterator<(K, V)> for BTreeMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let btree = BTreeMap::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item.0, item.1);
        });

        btree
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for BTreeMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    fn from(value: [(K, V); N]) -> Self {
        let btree: BTreeMap<K, V> = Default::default();

        value.into_iter().for_each(|(key, value)| {
            btree.insert(key, value);
        });

        btree
    }
}

impl<'a, K, V> IntoIterator for &'a BTreeMap<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Item = (&'a K, &'a V);

    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
