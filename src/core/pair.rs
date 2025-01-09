use core::cmp::Ordering;
use std::borrow::Borrow;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::fmt::Debug;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Hash)]
pub struct Pair<K: Ord, V> {
    pub key: K,
    pub value: V,
}

impl<K: Ord, V> Eq for Pair<K, V> {}

impl<K: Ord, V> PartialEq<Self> for Pair<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key.eq(&other.key)
    }
}

impl<K: Ord, V> PartialOrd<Self> for Pair<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Ord, V> Ord for Pair<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key.cmp(&other.key)
    }
}

impl<K: Ord, V> Borrow<K> for Pair<K, V> {
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
        assert_eq!(pair_one, pair_two);
    }

    #[test]
    fn node_like() {
        let mut vec = Vec::new();
        let p1 = Pair { key: 1, value: "a" };
        let p2 = Pair { key: 1, value: "b" };
        let p3 = Pair { key: 2, value: "c" };
     
        NodeLike::insert_set(&mut vec, p1.clone());
        NodeLike::insert_set(&mut vec, p2.clone());

        assert_eq!(vec.len(), 1);
    
        NodeLike::insert_set(&mut vec, p3.clone());
        assert!(vec.contains(&1));

        NodeLike::insert_set(&mut vec, p3.clone());
        assert_eq!(vec.len(), 2);
    }
}