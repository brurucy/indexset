use std::cmp::Ordering;
use std::sync::atomic::AtomicUsize;
use std::{borrow::Borrow, sync::Arc};

use parking_lot::{Mutex, RwLock};

use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

use scc::ebr::{AtomicShared, Guard, Shared, Tag};

use std::cell::UnsafeCell;
use std::fmt::{self, Debug};
use std::mem::{needs_drop, MaybeUninit};
use std::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use super::comparable::Equivalent;
use super::leaf::{InsertResult, Leaf, Scanner};

pub struct BTreeSet<T>
where
    T: Ord,
{
    node_capacity: usize,
    inner: RwLock<Vec<AtomicShared<Leaf<T, ()>>>>,
}
impl<T: Ord + 'static> Default for BTreeSet<T> {
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE;
        let leaf = Shared::new(Leaf::new());
        let inner_vec = vec![AtomicShared::from(leaf)];

        Self {
            node_capacity,
            inner: RwLock::new(inner_vec),
        }
    }
}

impl<T: Ord + Clone + 'static + Debug> BTreeSet<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&self, value: T) -> bool {
        loop {
            let global_read_lock = self.inner.read();
            let g = Guard::new();

            let mut node_idx = global_read_lock.partition_point(|node| {
                if let Some(&max) = node.load(Relaxed, &g).as_ref().unwrap().max_key().as_ref() {
                    return max.borrow() < &value;
                };
                false
            });

            if global_read_lock.get(node_idx).is_none() {
                node_idx -= 1
            }

            if let Some(node) = global_read_lock.get(node_idx).cloned() {
                let shared_node = node.get_shared(Acquire, &g).unwrap();
                match shared_node.insert(value.clone(), ()) {
                    InsertResult::Success => return true,
                    InsertResult::Duplicate(_, _) => return false,
                    InsertResult::Full(k, _) => {
                        drop(global_read_lock);
                        let split_result = {
                            let mut global_write_lock = self.inner.write();

                            if let Some(current_node) = global_write_lock.get(node_idx) {
                                if !current_node
                                    .load(Acquire, &g)
                                    .as_ptr()
                                    .equivalent(&shared_node.as_ptr())
                                {
                                    continue;
                                }

                                let mut low_key_leaf_shared = None;
                                let mut high_key_leaf_shared = None;

                                shared_node.freeze_and_distribute(
                                    &mut low_key_leaf_shared,
                                    &mut high_key_leaf_shared,
                                );

                                if let (Some(low), Some(high)) =
                                    (low_key_leaf_shared, high_key_leaf_shared)
                                {
                                    global_write_lock[node_idx]
                                        .swap((Some(low), Tag::None), Release);
                                    global_write_lock
                                        .insert(node_idx + 1, AtomicShared::from(high));
                                    true
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        };

                        if split_result {
                            continue;
                        }
                        return self.insert(k);
                    }
                    InsertResult::Frozen(k, _)
                    | InsertResult::Retired(k, _)
                    | InsertResult::Retry(k, _) => return self.insert(k),
                }
            }
            return false;
        }
    }
    fn locate_node<Q>(&self, value: &Q, g: &Guard) -> Option<Shared<Leaf<T, ()>>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let global_read_lock = self.inner.read();
        let mut node_idx = global_read_lock.partition_point(|node| {
            if let Some(&ref max) = node.load(Acquire, &g).as_ref().unwrap().max_key() {
                return max.borrow() < value;
            };
            false
        });
        // When value is greater than all elements inside inner[node_idx], then len
        // of inner[node_idx], which is not a valid place for insertion, is returned. It will
        // never return less than 0, so it is only necessary to check whether it is out of bounds
        // from the right
        if global_read_lock.get(node_idx).is_none() {
            node_idx -= 1
        }
        global_read_lock
            .get(node_idx)
            .map(|x| x.get_shared(Relaxed, g).unwrap())
    }
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized + Debug,
    {
        let g = Guard::new();
        if let Some(node) = self.locate_node(value, &g) {
            let (potential_kv, metadata) = node.min_greater_equal(value);
            if let Some(kv) = potential_kv {
                return kv.0.borrow() == value;
            }
        }

        false
    }
    pub fn len(&self) -> usize {
        let global_read_lock = self.inner.read();
        let g = Guard::new();
        global_read_lock
            .iter()
            .map(|node| {
                let leaf = node.load(Relaxed, &g).as_ref().unwrap();
                let count = Scanner::new(leaf).count();
                count
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use crate::concurrent2::metadata::Dimension;
    use crate::concurrent2::set::BTreeSet;
    use rand::Rng;
    use scc::ebr::Guard;
    use std::collections::HashSet;
    use std::sync::{Arc, Mutex};
    use std::thread;

    #[test]
    fn test_concurrent_insert() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let num_threads = 8;
        let operations_per_thread = 10000;
        let mut handles = vec![];

        let test_data: Vec<Vec<(i32, i32)>> = (0..num_threads)
            .map(|_| {
                let mut rng = rand::thread_rng();
                (0..operations_per_thread)
                    .map(|_| {
                        let value = rng.gen_range(0..10000);
                        let operation = rng.gen_range(0..2);
                        (operation, value)
                    })
                    .collect()
            })
            .collect();

        let expected_values = Arc::new(Mutex::new(HashSet::new()));

        for thread_idx in 0..num_threads {
            let set_clone = Arc::clone(&set);
            let expected_values = Arc::clone(&expected_values);
            let thread_data = test_data[thread_idx].clone();

            let handle = thread::spawn(move || {
                for (operation, value) in thread_data {
                    if operation == 0 {
                        set_clone.insert(value);
                        expected_values.lock().unwrap().insert(value);
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let expected_values = expected_values.lock().unwrap();
        assert_eq!(set.len(), expected_values.len());

        for value in expected_values.iter() {
            assert!(set.contains(value), "Missing value: {}", value);
        }
    }

    #[test]
    fn test_insert_st() {
        let set = Arc::new(BTreeSet::<usize>::new());
        let n = 1024;
        let range = 0..n;
        for i in range.rev() {
            set.insert(i);
        }

        let g = Guard::new();
        let zeroth = (set.inner.read())[0]
            .load(std::sync::atomic::Ordering::Relaxed, &g)
            .get_shared()
            .unwrap();
        println!("Zeroth - {:?}", unsafe {
            zeroth
                .entry_array
                .get()
                .read()
                .0
                .map(|munit| munit.assume_init())
        });
        // println!(
        //     "Zeroth State - { }",
        //     Dimension::frozen_bytes(zeroth.load_bytes(std::sync::atomic::Ordering::Relaxed))
        // );
        let first = (set.inner.read())[1]
            .load(std::sync::atomic::Ordering::Relaxed, &g)
            .get_shared()
            .unwrap();

        println!("First - {:?}", unsafe {
            first
                .entry_array
                .get()
                .read()
                .0
                .map(|munit| munit.assume_init())
        });
        // println!(
        //     "First State - {}",
        //     Dimension::frozen_bytes(first.load_bytes(std::sync::atomic::Ordering::Relaxed))
        // );

        println!("Leaf count: {:?}", set.inner.read().len());

        assert_eq!(set.len(), n);
        for i in 0..n {
            assert!(set.contains(&i), "{} wasn't found", i);
        }
        assert!(!set.contains(&n));
    }
}
