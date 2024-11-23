use std::{borrow::Borrow, sync::Arc};

use parking_lot::{Mutex, RwLock};

use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

#[derive(Debug)]
pub struct BTreeSet<T>
where
    T: Ord,
{
    node_capacity: usize,
    inner: RwLock<Vec<Arc<Mutex<Vec<T>>>>>,
}
impl<T: Ord> Default for BTreeSet<T> {
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE / 8;

        Self {
            node_capacity,
            inner: RwLock::new(vec![Arc::new(Mutex::new(Vec::with_capacity(
                node_capacity,
            )))]),
        }
    }
}

impl<T: Ord + Clone> BTreeSet<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&self, value: T) -> bool {
        let global_read_lock = self.inner.read();
        let mut node_idx = global_read_lock.partition_point(|node| {
            if let Some(&max) = node.lock().last().as_ref() {
                return max.borrow() < &value;
            };
            false
        });
        if global_read_lock.get(node_idx).is_none() {
            node_idx -= 1
        }
        if let Some(node) = global_read_lock.get(node_idx).cloned() {
            let mut node_write_lock = node.lock();
            if node_write_lock.len() == self.node_capacity {
                if NodeLike::insert(&mut *node_write_lock, value) {
                    drop(global_read_lock);
                    drop(node_write_lock);
                    let mut global_write_lock = self.inner.write();
                    let mut node_write_lock = node.lock();
                    let new_node = node_write_lock.halve();
                    global_write_lock.insert(node_idx + 1, Arc::new(Mutex::new(new_node)));

                    return true;
                }
            } else {
                return NodeLike::insert(&mut *node_write_lock, value);
            }
        }

        false
    }
    fn locate_node<Q>(&self, value: &Q) -> Option<Arc<Mutex<Vec<T>>>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let global_read_lock = self.inner.read();
        let mut node_idx = global_read_lock.partition_point(|node| {
            if let Some(&max) = node.lock().last().as_ref() {
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
        global_read_lock.get(node_idx).cloned()
    }
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(node) = self.locate_node(value) {
            return node.lock().contains(value);
        }
        false
    }
    pub fn len(&self) -> usize {
        let global_read_lock = self.inner.read();
        global_read_lock.iter().map(|node| node.lock().len()).sum()
    }
}

#[cfg(test)]
mod tests {
    use crate::concurrent2::set::BTreeSet;
    use rand::Rng;
    use std::collections::HashSet;
    use std::sync::{Arc, Mutex};
    use std::thread;

    #[test]
    fn test_concurrent_insert() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let num_threads = 8;
        let operations_per_thread = 1000;
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
                        //if set_clone.insert(value) {
                        expected_values.lock().unwrap().insert(value);
                        //}
                    }
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let expected_values = expected_values.lock().unwrap();
        println!("AAA {}", set.len());
        assert_eq!(set.len(), expected_values.len());

        for value in expected_values.iter() {
            assert!(set.contains(value), "Missing value: {}", value);
        }
    }

    #[test]
    fn test_insert_st() {
        let set = Arc::new(BTreeSet::<i32>::new());
        let range = 0..100_000;
        for i in range {
            set.insert(i);
        }

        assert_eq!(set.len(), 100_000);
        for i in 0..100_000 {
            set.contains(&i);
        }
    }
}
