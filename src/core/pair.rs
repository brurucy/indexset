use core::cmp::Ordering;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Hash)]
pub struct Pair<K: Ord, #[cfg(not(feature = "multiset"))] V, #[cfg(feature = "multiset")] V: PartialEq> {
    pub key: K,
    pub value: V,
}

impl<K: Ord, #[cfg(not(feature = "multiset"))] V, #[cfg(feature = "multiset")] V: PartialEq> Eq for Pair<K, V> {}

#[cfg(not(feature = "multiset"))]
impl<K, V> PartialEq<Self> for Pair<K, V>
where
    K: Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

#[cfg(feature = "multiset")]
impl<K, V> PartialEq<Self> for Pair<K, V>
where
    K: Ord,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.value == other.value
    }
}

impl<K: Ord, #[cfg(not(feature = "multiset"))] V, #[cfg(feature = "multiset")] V: PartialEq> PartialOrd<Self> for Pair<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Ord, #[cfg(not(feature = "multiset"))] V, #[cfg(feature = "multiset")] V: PartialEq> Ord for Pair<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl<K: Ord, #[cfg(not(feature = "multiset"))] V, #[cfg(feature = "multiset")] V: PartialEq> Borrow<K> for Pair<K, V> {
    fn borrow(&self) -> &K {
        &self.key
    }
}