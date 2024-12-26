use core::cmp::Ordering;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone)]
pub struct Pair<K, V> {
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

impl<K, V> Hash for Pair<K, V>
where
    K: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&self.key, state);
    }
}

impl<K, V> PartialOrd<Self> for Pair<K, V>
where
    K: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
