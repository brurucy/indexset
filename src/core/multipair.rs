use std::fmt::Debug;
use std::{borrow::Borrow, mem::MaybeUninit};

use core::cmp::Ordering;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use fastrand;

use crate::core::pair::Pair;

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug, Clone, Hash)]
pub struct MultiPair<K, V> {
    pub key: K,
    pub value: V,
    pub discriminator: u64,
}

impl<K: Ord, V: PartialEq> MultiPair<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value, discriminator: fastrand::u64(..) }
    }
    pub fn with_infimum(key: K) -> Self {
        Self { key, value: unsafe { MaybeUninit::uninit().assume_init() }, discriminator: INFIMUM }
    }
    pub fn with_supremum(key: K) -> Self {
        Self { key, value: unsafe { MaybeUninit::uninit().assume_init() }, discriminator: SUPREMUM }
    }
}

impl<K: Ord, V: PartialEq> Eq for MultiPair<K, V> {}

impl<K: Ord, V: PartialEq> PartialEq<Self> for MultiPair<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key.eq(&other.key) && self.value.eq(&other.value)
    }
}

const INFIMUM: u64 = 0;
const SUPREMUM: u64 = u64::MAX;

impl<K: Ord, V: PartialEq> Ord for MultiPair<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.key.cmp(&other.key) {
            Ordering::Equal => {
                if (self.discriminator == INFIMUM || other.discriminator == INFIMUM) || (self.discriminator == SUPREMUM || other.discriminator == SUPREMUM) {
                    return self.discriminator.cmp(&other.discriminator);
                }

                if self.value.eq(&other.value) {
                    return Ordering::Equal;
                }

                self.discriminator.cmp(&other.discriminator)
            },
            ord => ord,
        }
    }
}

impl<K: Ord, V: PartialEq> PartialOrd for MultiPair<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<K: Ord, V: PartialEq> Borrow<K> for MultiPair<K, V> {
    fn borrow(&self) -> &K {
        &self.key
    }
}

impl<K: Ord, V: PartialEq> From<Pair<K, V>> for MultiPair<K, V> {
    fn from(pair: Pair<K, V>) -> Self {
        MultiPair {
            key: pair.key,
            value: pair.value,
            discriminator: fastrand::u64(..),
        }
    }
}

impl<K: Ord, V: PartialEq> From<MultiPair<K, V>> for Pair<K, V> {
    fn from(pair: MultiPair<K, V>) -> Self {
        Pair {
            key: pair.key,
            value: pair.value,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::core::node::NodeLike;
    use std::ops::Bound::*;

    #[test]
    fn borrow_test() {
        let pair = MultiPair::new(1usize, 2usize);
        assert_eq!(<MultiPair<usize, usize> as Borrow<usize>>::borrow(&pair), &1usize);
    }

    #[test]
    fn eq_test() {
        let pair_one = MultiPair::new(1usize, 2usize);
        let pair_two = MultiPair::new(1usize, 3usize);
        assert_ne!(pair_one, pair_two);
    }

    #[test]
    fn node_like() {
        let mut vec = Vec::new();
        let p1 = MultiPair::new(1, "a");
        let p2 = MultiPair::new(1, "b");
        let p3 = MultiPair::new(2, "c");
     
        NodeLike::insert(&mut vec, p1.clone());
        NodeLike::insert(&mut vec, p2.clone());
        assert_eq!(vec.len(), 2); 

        NodeLike::insert(&mut vec, p1.clone());
        assert_eq!(vec.len(), 2);
     
        NodeLike::insert(&mut vec, p3.clone());
        assert_eq!(vec.len(), 3);
     }

     #[test]
     fn range_bounds() {
        let mut vec = Vec::new();
    
        let p1a = MultiPair::new(1, "a");
        let p1b = MultiPair::new(1, "b");
        let p1c = MultiPair::new(1, "c");
        let p2a = MultiPair::new(2, "a");
        let p2b = MultiPair::new(2, "b");
        let p3a = MultiPair::new(3, "a");
        let p3b = MultiPair::new(3, "b");
        let p3c = MultiPair::new(3, "c");
        let p3d = MultiPair::new(3, "d");
        let p4a = MultiPair::new(4, "a");

        NodeLike::insert(&mut vec, p4a.clone());
        NodeLike::insert(&mut vec, p1a.clone());
        NodeLike::insert(&mut vec, p1c.clone());
        NodeLike::insert(&mut vec, p1b.clone());
        NodeLike::insert(&mut vec, p2b.clone());
        NodeLike::insert(&mut vec, p2a.clone());
        NodeLike::insert(&mut vec, p3a.clone());
        NodeLike::insert(&mut vec, p3b.clone());
        NodeLike::insert(&mut vec, p3d.clone());
        NodeLike::insert(&mut vec, p3c.clone());
        assert_eq!(vec.len(), 10);

        let start_1 = vec.rank(Included(&MultiPair::with_infimum(1)), true).or_else(|| Some(0)).unwrap();
        let end_1 = vec.rank(Excluded(&MultiPair::with_supremum(1)), true).unwrap();
        let range_1 = &vec[start_1..=end_1];
        assert_eq!(range_1.len(), 3);
        assert!(range_1.contains(&p1a));
        assert!(range_1.contains(&p1b));
        assert!(range_1.contains(&p1c));

        let end_2 = vec.rank(Excluded(&MultiPair::with_supremum(2)), true).unwrap();
        let range_2 = &vec[start_1..=end_2];
        assert_eq!(range_2.len(), 5);
        assert!(range_2.contains(&p1a));
        assert!(range_2.contains(&p1b));
        assert!(range_2.contains(&p1c));
        assert!(range_2.contains(&p2a));
        assert!(range_2.contains(&p2b));
        assert_ne!(range_2.contains(&p3a), true);

        let start_3 = vec.rank(Included(&MultiPair::with_infimum(3)), true).unwrap() + 1;
        let end_3 = vec.rank(Excluded(&MultiPair::with_supremum(3)), true).unwrap();
        let range_3 = &vec[start_3..=end_3];
        assert_eq!(range_3.len(), 4);
        assert!(range_3.contains(&p3a));
        assert!(range_3.contains(&p3b));
        assert!(range_3.contains(&p3c));
        assert!(range_3.contains(&p3d));

        let start_4 = vec.rank(Included(&MultiPair::with_infimum(4)), true).unwrap() + 1;
        let end_4 = vec.rank(Excluded(&MultiPair::with_supremum(4)), true).unwrap();
        let range_4 = &vec[start_4..=end_4];
        assert_eq!(range_4.len(), 1);
        assert!(range_4.contains(&p4a));
     }
}
