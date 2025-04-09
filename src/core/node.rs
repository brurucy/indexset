use core::borrow::Borrow;
use core::cmp::Ordering;
use std::ops::Deref;

pub trait NodeLike<T: Ord> {
    #[allow(dead_code)]
    fn with_capacity(capacity: usize) -> Self;
    #[allow(dead_code)]
    fn get_ith(&self, index: usize) -> Option<&T>;
    #[allow(dead_code)]
    fn halve(&mut self) -> Self;
    #[allow(dead_code)]
    fn len(&self) -> usize;
    #[allow(dead_code)]
    fn capacity(&self) -> usize;
    #[allow(dead_code)]
    fn insert(&mut self, value: T) -> (bool, usize);
    #[allow(dead_code)]
    fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn try_select<Q: Ord + ?Sized>(&self, value: &Q) -> Option<usize>
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn rank<Q: Ord + ?Sized>(&self, bound: std::ops::Bound<&Q>, from_start: bool) -> Option<usize>
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn delete<Q: Ord + ?Sized>(&mut self, value: &Q) -> Option<(T, usize)>
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn replace(&mut self, idx: usize, value: T) -> Option<T>;
    #[allow(dead_code)]
    fn max(&self) -> Option<&T>;
    #[allow(dead_code)]
    fn min(&self) -> Option<&T>;
    #[allow(dead_code)]
    fn iter<'a>(&'a self) -> std::slice::Iter<'a, T> where T: 'a;
}

#[inline]
fn search<Q, T: Ord>(haystack: &[T], needle: &Q) -> Result<usize, usize>
where
    T: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    let mut j = haystack.len();

    unsafe {
        let mut i = 0;
        let p = haystack.as_ptr().cast::<T>();
        let mut m = j >> 1;
        while i != j {
            match (*p.add(m)).borrow().cmp(&needle) {
                Ordering::Equal => return Ok(m),
                Ordering::Less => {
                    i = m + 1;
                    m = (i + j) >> 1;
                }
                Ordering::Greater => {
                    j = m;
                    m = (i + j) >> 1;
                }
            }
        }
        Err(i)
    }
}

enum Direction<'a, T> {
    Forward(std::slice::Iter<'a, T>),
    Backward(std::iter::Rev<std::slice::Iter<'a, T>>),
}

#[inline]
fn compute_positions_to_skip<Q, T: Ord>(haystack: &[T], bound: std::ops::Bound<&Q>, forward: bool) -> Option<usize>
where
    T: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    match bound {
        // If the bound is unbounded, then no skipping is needed
        std::ops::Bound::Unbounded => { None }
        std::ops::Bound::Included(value) | std::ops::Bound::Excluded(value) => {
            let mut positions_to_skip = -1;
            let iter = if forward {
                Direction::Forward(haystack.iter())
            } else {
                Direction::Backward(haystack.iter().rev())
            };

            match iter {
                Direction::Forward(iter) => {
                    for item in iter {
                        match item.borrow().cmp(&value) {
                            Ordering::Less => positions_to_skip += 1,
                                Ordering::Equal => match bound {
                                std::ops::Bound::Included(_) => break,
                                std::ops::Bound::Excluded(_) => { positions_to_skip += 1; break },
                                _ => unreachable!(),
                            },
                            Ordering::Greater => break,
                        }
                    }
                }
                Direction::Backward(iter) => {
                    for item in iter {
                        match item.borrow().cmp(&value) {
                            Ordering::Greater => positions_to_skip += 1,
                            Ordering::Equal => match bound {
                                std::ops::Bound::Included(_) => break,
                                std::ops::Bound::Excluded(_) => { positions_to_skip += 1; break },
                                _ => unreachable!(),
                            },
                            Ordering::Less => break,
                        }
                    }
                }
            }

            if positions_to_skip >= 0 {
                Some(positions_to_skip as usize)
            } else {
                None
            }
        }
    }
}

impl<T: Ord> NodeLike<T> for Vec<T> {
    fn with_capacity(capacity: usize) -> Self {
        Vec::with_capacity(capacity)
    }
    #[inline]
    fn get_ith(&self, index: usize) -> Option<&T> {
        self.get(index)
    }
    #[inline]
    fn halve(&mut self) -> Self {
        self.split_off(self.capacity() / 2)
    }
    #[inline]
    fn len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn capacity(&self) -> usize {
        self.capacity()
    }
    #[inline]
    fn insert(&mut self, value: T) -> (bool, usize) {
        match search(&self, &value) {
            Ok(idx) => (false, idx),
            Err(idx) => {
                self.insert(idx, value);
                (true, idx)
            }
        }
    }
    #[inline]
    fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match search(&self, &value) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
    #[inline]
    fn try_select<Q>(&self, value: &Q) -> Option<usize>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match search(&self, &value) {
            Ok(index) => Some(index),
            Err(_) => None,
        }
    }
    #[inline]
    fn rank<Q>(&self, bound: std::ops::Bound<&Q>, from_start: bool) -> Option<usize>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        compute_positions_to_skip(&self, bound, from_start)
    }
    #[inline]
    fn delete<Q>(&mut self, value: &Q) -> Option<(T, usize)>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match search(&self, value) {
            Ok(idx) => Some((self.remove(idx), idx)),
            Err(_) => None,
        }
    }
    #[inline]
    fn replace(&mut self, idx: usize, value: T) -> Option<T> {
        if let Some(old) = self.get_mut(idx) {
            let old = std::mem::replace(old, value);
            return Some(old);
        }

        None
    }
    #[inline]
    fn max(&self) -> Option<&T> {
        self.last()
    }

    fn min(&self) -> Option<&T> {
        self.first()
    }

    #[inline]
    fn iter<'a>(&'a self) -> std::slice::Iter<'a, T>
    where T: 'a
    {
        self.deref().iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_search_bound() {
        let vec = vec![1, 3, 5, 7, 9];

        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Unbounded, true), None);
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Unbounded, false), None);

        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&1), true), None);
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&5), true), Some(1));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&9), true), Some(3));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&0), true), None);
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&10), true), Some(4));

        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&1), true), Some(0));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&5), true), Some(2));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&9), true), Some(4));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&0), true), None);
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&10), true), Some(4));

        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&1), false), Some(3));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&5), false), Some(1));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&9), false), None);
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&0), false), Some(4));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Included(&10), false), None);

        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&1), false), Some(4));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&5), false), Some(2));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&9), false), Some(0));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&0), false), Some(4));
        assert_eq!(compute_positions_to_skip(&vec, std::ops::Bound::Excluded(&10), false), None);

        let empty: Vec<i32> = vec![];
        assert_eq!(compute_positions_to_skip(&empty, std::ops::Bound::Included(&1), true), None);
        assert_eq!(compute_positions_to_skip(&empty, std::ops::Bound::Excluded(&1), false), None);
    }

}
