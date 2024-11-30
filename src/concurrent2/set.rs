use std::fmt::Debug;
use std::{borrow::Borrow, sync::Arc};

use crossbeam_skiplist::SkipMap;
use parking_lot::Mutex;
use parking_lot::RwLock;

use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

#[derive(Debug)]
pub struct BTreeSet<T>
where
    T: Ord + Clone + 'static,
{
    node_capacity: usize,
    index: SkipMap<T, Arc<Mutex<Vec<T>>>>,
    index_lock: RwLock<()>,
}
impl<T: Ord + Clone + 'static> Default for BTreeSet<T> {
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE;
        let index = SkipMap::new();

        Self {
            node_capacity,
            index,
            index_lock: RwLock::new(()),
        }
    }
}

impl<T: Ord + Clone + Send + Debug> BTreeSet<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&self, value: T) -> bool {
        loop {
            let mut _index_write_guard = self.index_lock.read();
            let target_node = match self.index.lower_bound(std::ops::Bound::Included(&value)) {
                Some(entry) => entry.value().clone(),
                None => self
                    .index
                    .back()
                    .map(|last| last.value().clone())
                    .or_else(|| Some(Arc::new(Mutex::new(Vec::with_capacity(self.node_capacity)))))
                    .unwrap(),
            };

            let mut node_write_lock = target_node.lock();
            if node_write_lock.len() >= self.node_capacity {
                if NodeLike::insert(&mut *node_write_lock, value.clone()) {
                    drop(node_write_lock);
                    drop(_index_write_guard);
                    let _index_write_guard = self.index_lock.write();
                    node_write_lock = target_node.lock();

                    if let Some(old_max) = node_write_lock.last().cloned() {
                        self.index.remove(&old_max);
                    }
                    let new_node_vec = node_write_lock.halve();
                    if let Some(max) = node_write_lock.last().cloned() {
                        self.index.insert(max, target_node.clone());
                    }

                    let new_node = Arc::new(Mutex::new(new_node_vec));
                    if let Some(max) = new_node.lock().last().cloned() {
                        self.index.insert(max, new_node.clone());
                    }

                    return true;
                };

                break;
            } else {
                let old_max = node_write_lock.last().cloned();
                let inserted = NodeLike::insert(&mut *node_write_lock, value.clone());
                if inserted {
                    if let Some(new_max) = node_write_lock.last().cloned() {
                        drop(node_write_lock);
                        if Some(&new_max) != old_max.as_ref() {
                            drop(_index_write_guard);
                            let _index_write_guard = self.index_lock.write();
                            if let Some(old_max) = old_max {
                                self.index.remove(&old_max);
                            }

                            self.index.insert(new_max, target_node.clone());
                        }
                    }
                }

                return inserted;
            }
        }

        false
    }
    fn locate_node<Q>(&self, value: &Q) -> Option<Arc<Mutex<Vec<T>>>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.index.lower_bound(std::ops::Bound::Included(&value)) {
            Some(entry) => Some(entry.value().clone()),
            None => self
                .index
                .back()
                .map(|last| last.value().clone())
                .or_else(|| self.index.front().map(|first| first.value().clone())),
        }
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
        self.index
            .iter()
            .map(|node| node.value().lock().len())
            .sum()
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
        let num_threads = 16;
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
        let set = Arc::new(BTreeSet::<i32>::new());
        let mut rng = rand::thread_rng();

        let range = 0..100000;
        let mut inserted_values = HashSet::new();
        for _ in range {
            let value = rng.gen_range(0..100000);
            if inserted_values.insert(value) {
                assert!(set.insert(value));
            }
        }

        assert_eq!(
            set.len(),
            inserted_values.len(),
            "Length did not match: {:?}",
            set.index.iter().collect::<Vec<_>>()
        );
        for i in inserted_values {
            assert!(
                set.contains(&i),
                "Did not find: {} with index: {:?}",
                i,
                set.index.iter().collect::<Vec<_>>(),
            );
        }
    }
}
