use crate::core::constants::DEFAULT_CUTOFF;
use core::borrow::Borrow;
use core::cmp::Ordering;

pub trait NodeLike<T: Ord> {
    #[allow(dead_code)]
    fn get_ith(&self, index: usize) -> Option<&T>;
    #[allow(dead_code)]
    fn halve(&mut self) -> Self;
    #[allow(dead_code)]
    fn len(&self) -> usize;
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
    fn rank<Q: Ord + ?Sized>(&self, bound: std::ops::Bound<&Q>, from_start: bool) -> usize
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

#[inline]
fn search_bound<Q, T: Ord>(haystack: &[T], bound: std::ops::Bound<&Q>, from_start: bool) -> usize
where
    T: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    match bound {
        std::ops::Bound::Unbounded => {
            if from_start {
                0
            } else {
                haystack.len()
            }
        }
        std::ops::Bound::Included(value) | std::ops::Bound::Excluded(value) => {
            let mut i = 0;
            while i < haystack.len() {
                match haystack[i].borrow().cmp(&value) {
                    Ordering::Less => i += 1,
                    Ordering::Equal => match bound {
                        std::ops::Bound::Included(_) => return i,
                        std::ops::Bound::Excluded(_) => return i + 1,
                        _ => unreachable!(),
                    },
                    Ordering::Greater => break,
                }
            }
            i
        }
    }
}

impl<T: Ord> NodeLike<T> for Vec<T> {
    #[inline]
    fn get_ith(&self, index: usize) -> Option<&T> {
        self.get(index)
    }
    #[inline]
    fn halve(&mut self) -> Self {
        self.split_off(DEFAULT_CUTOFF)
    }
    #[inline]
    fn len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn insert(&mut self, value: T) -> (bool, usize) {
        match search(&self, &value) {
            Ok(idx) => {
                #[cfg(not(feature = "multiset"))]
                return(false, idx);

                #[cfg(feature = "multiset")]
                if self[idx] == value {
                    return (false, idx)
                }

                self.insert(idx, value);
                (true, idx)
            }
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
    fn rank<Q>(&self, bound: std::ops::Bound<&Q>, from_start: bool) -> usize
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        search_bound(&self, bound, from_start)
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
}
