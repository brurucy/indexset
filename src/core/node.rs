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
    fn insert(&mut self, value: T) -> bool;
    #[allow(dead_code)]
    fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn delete<Q: Ord + ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>;
    #[allow(dead_code)]
    fn replace(&mut self, value: T) -> Option<T>;
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
            match (*p.add(m)).borrow().cmp(needle) {
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
    fn insert(&mut self, value: T) -> bool {
        match search(&self, &value) {
            Ok(_) => return false,
            Err(idx) => {
                self.insert(idx, value);
            }
        }

        true
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
    fn delete<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q> + Ord,
        Q: Ord + ?Sized,
    {
        match search(&self, value) {
            Ok(idx) => Some(self.remove(idx)),
            Err(_) => None,
        }
    }
    #[inline]
    fn replace(&mut self, value: T) -> Option<T> {
        match search(&self, &value) {
            Ok(idx) => {
                self.push(value);
                let len = self.len() - 1;
                self.swap(idx, len);

                self.pop()
            }
            Err(_) => None,
        }
    }
    #[inline]
    fn max(&self) -> Option<&T> {
        self.last()
    }
}
