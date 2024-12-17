use core::cmp::Ordering;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::borrow::Borrow;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Hash)]
pub struct Pair<K, V>
where
    K: Ord,
{
    pub key: K,
    pub value: V,
}

impl<K, V> Eq for Pair<K, V> where K: Ord {}

impl<K, V> PartialEq<Self> for Pair<K, V>
where
    K: Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl<K, V> PartialOrd<Self> for Pair<K, V>
where
    K: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K, V> Ord for Pair<K, V>
where
    K: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl<K: Ord, V> Borrow<K> for Pair<K, V> {
    fn borrow(&self) -> &K {
        &self.key
    }
}

impl<K: Ord, V> Pair<K, V> {
    pub fn replace(&mut self, value: V) -> V {
        let old_value = std::mem::replace(&mut self.value, value);

        old_value
    }
}
