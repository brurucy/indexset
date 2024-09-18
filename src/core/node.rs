use core::borrow::Borrow;
use core::cmp::Ordering;

pub trait NodeLike<T: Ord>: Default {
    #[allow(dead_code)]
    fn get_ith(&self, index: usize) -> Option<&T>;
    #[allow(dead_code)]
    fn halve(&mut self) -> Self;
    #[allow(dead_code)]
    fn len(&self) -> usize;
    #[allow(dead_code)]
    fn insert(&mut self, value: T) -> bool;
    #[allow(dead_code)]
    fn contains(&self, value: &T) -> bool;
    #[allow(dead_code)]
    fn delete(&mut self, index: usize) -> T;
    #[allow(dead_code)]
    fn max(&self) -> Option<&T>;
}

#[inline]
fn search<T: Ord>(haystack: &[T], needle: &T) -> Result<usize, usize> {
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
        self.split_off(super::constants::DEFAULT_CUTOFF)
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
    fn contains(&self, value: &T) -> bool {
        match search(&self, &value) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
    #[inline]
    fn delete(&mut self, index: usize) -> T {
        self.remove(index)
    }
    #[inline]
    fn max(&self) -> Option<&T> {
        self.last()
    }
}
