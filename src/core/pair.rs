use core::cmp::Ordering;
use std::borrow::Borrow;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::fmt::Debug;

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::core::node::NodeLike;

    #[test]
    fn borrow_test() {
        let pair = Pair { key: 1usize, value: 2usize };
        assert_eq!(<Pair<usize, usize> as Borrow<usize>>::borrow(&pair), &1usize);
    }

    #[test]
    fn eq_test() {
        let pair_one = Pair { key: 1usize, value: 2usize };
        let pair_two = Pair { key: 1usize, value: 3usize };
        #[cfg(not(feature = "multiset"))]
        assert_eq!(pair_one, pair_two);
        #[cfg(feature = "multiset")]
        assert_ne!(pair_one, pair_two);
    }

    #[test]
    fn node_like() {
        let mut vec = Vec::new();
        let p1 = Pair { key: 1, value: "a" };
        let p2 = Pair { key: 1, value: "b" };
        let p3 = Pair { key: 2, value: "c" };
     
        NodeLike::insert(&mut vec, p1.clone());
        
        #[cfg(not(feature = "multiset"))]
        {
            NodeLike::insert(&mut vec, p2.clone());
            assert_eq!(vec.len(), 1);
        }
        
        #[cfg(feature = "multiset")]
        {
            NodeLike::insert(&mut vec, p2.clone());
            assert_eq!(vec.len(), 2); 
        }
     
        NodeLike::insert(&mut vec, p3.clone());
        assert!(vec.contains(&1));
     }
}
