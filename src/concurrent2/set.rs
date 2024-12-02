use std::fmt::Debug;
use std::{borrow::Borrow, sync::Arc};

use crossbeam_skiplist::SkipMap;
use crossbeam_utils::sync::ShardedLock;
use parking_lot::{ArcMutexGuard, Mutex, RawMutex};

use crate::core::constants::DEFAULT_INNER_SIZE;
use crate::core::node::*;

type Node<T> = Arc<Mutex<Vec<T>>>;

#[derive(Debug)]
pub struct BTreeSet<T>
where
    T: Ord + Clone + 'static,
{
    node_capacity: usize,
    index: SkipMap<T, Node<T>>,
    index_lock: ShardedLock<()>,
}
impl<T: Ord + Clone + 'static> Default for BTreeSet<T> {
    fn default() -> Self {
        let node_capacity = DEFAULT_INNER_SIZE;
        let index = SkipMap::new();

        Self {
            node_capacity,
            index,
            index_lock: ShardedLock::new(()),
        }
    }
}

type OldVersion<T> = Node<T>;
type CurrentVersion<T> = Node<T>;

enum Operation<T: Send> {
    Split(OldVersion<T>, T, T),
    UpdateMax(CurrentVersion<T>, T),
}

impl<T: Ord + Send + Clone + 'static> Operation<T> {
    fn commit(self, index: &SkipMap<T, Node<T>>) -> bool {
        match self {
            Operation::Split(old_node, old_max, value) => {
                let mut guard = old_node.lock_arc();
                if let Some(entry) = index.get(&old_max) {
                    if Arc::ptr_eq(entry.value(), &old_node) {
                        index.remove(&old_max);

                        let mut new_vec = guard.halve();

                        let mut inserted = false;
                        let mut insert_attempted = false;
                        if let Some(max) = guard.last().cloned() {
                            if max >= value {
                                inserted = NodeLike::insert(&mut *guard, value.clone());
                                insert_attempted = true;
                            }

                            index.insert(max, old_node.clone());
                        }

                        if let Some(max) = new_vec.last().cloned() {
                            if !insert_attempted {
                                inserted = NodeLike::insert(&mut new_vec, value.clone());
                            }

                            index.insert(max, Arc::new(Mutex::new(new_vec)));
                        }

                        return inserted;
                    }
                }

                false
            }
            Operation::UpdateMax(node, old_max) => {
                let guard = node.lock_arc();
                let new_max = guard.last().unwrap();
                if let Some(entry) = index.get(&old_max) {
                    if Arc::ptr_eq(entry.value(), &node) {
                        match new_max.cmp(&old_max) {
                            std::cmp::Ordering::Less => panic!("new_max is smaller than old_max?"),
                            std::cmp::Ordering::Equal => return true,
                            std::cmp::Ordering::Greater => {
                                index.remove(&old_max);
                                index.insert(new_max.clone(), node.clone());

                                return true;
                            }
                        }
                    }
                }

                false
            }
        }
    }
}

pub struct Ref<T: Ord + Clone + Send> {
    node_guard: ArcMutexGuard<RawMutex, Vec<T>>,
    position: usize,
}

impl<T: Ord + Clone + Send> Ref<T> {
    fn get(&self) -> &T {
        self.node_guard.get(self.position).unwrap()
    }
}

impl<T: Ord + Clone + Send + Debug> BTreeSet<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn insert(&self, value: T) -> bool {
        loop {
            let mut _global_guard = self.index_lock.read();
            let target_node_entry = match self.index.lower_bound(std::ops::Bound::Included(&value))
            {
                Some(entry) => entry,
                None => {
                    if let Some(last) = self.index.back() {
                        last
                    } else {
                        let mut first_vec = Vec::with_capacity(self.node_capacity);
                        first_vec.push(value.clone());

                        let first_node = Arc::new(Mutex::new(first_vec));

                        drop(_global_guard);
                        if let Ok(_) = self.index_lock.try_write() {
                            self.index.insert(value.clone(), first_node);

                            return true;
                        }

                        continue;
                    }
                }
            };

            let mut node_guard = target_node_entry.value().lock_arc();
            let mut operation = None;
            if node_guard.len() < self.node_capacity {
                let old_max = node_guard.last().cloned();
                let inserted = NodeLike::insert(&mut *node_guard, value.clone());
                if inserted {
                    if node_guard.last().cloned() == old_max {
                        return true;
                    }

                    if old_max.is_some() {
                        operation = Some(Operation::UpdateMax(
                            target_node_entry.value().clone(),
                            old_max.unwrap(),
                        ))
                    }
                } else {
                    return false;
                }
            } else {
                operation = Some(Operation::Split(
                    target_node_entry.value().clone(),
                    target_node_entry.key().clone(),
                    value.clone(),
                ))
            }

            drop(_global_guard);
            drop(node_guard);
            let _global_guard = self.index_lock.write();

            if operation.unwrap().commit(&self.index) {
                return true;
            }
            drop(_global_guard);

            continue;
        }
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
    pub fn get<'a, Q>(&'a self, value: &'a Q) -> Option<Ref<T>>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(node) = self.locate_node(value) {
            let node_guard = node.lock_arc();
            let potential_position = node_guard.try_select(value);

            if let Some(position) = potential_position {
                return Some(Ref {
                    node_guard,
                    position,
                });
            }
        }

        None
    }
    pub fn len(&self) -> usize {
        self.index
            .iter()
            .map(|node| node.value().lock().len())
            .sum()
    }
}

impl<T> FromIterator<T> for BTreeSet<T>
where
    T: Ord + Clone + Send + Debug,
{
    fn from_iter<K: IntoIterator<Item = T>>(iter: K) -> Self {
        let btree = BTreeSet::new();
        iter.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

impl<T, const N: usize> From<[T; N]> for BTreeSet<T>
where
    T: Ord + Clone + Send + Debug,
{
    fn from(value: [T; N]) -> Self {
        let btree: BTreeSet<T> = Default::default();

        value.into_iter().for_each(|item| {
            btree.insert(item);
        });

        btree
    }
}

pub struct Iter<'a, T>
where
    T: Ord + Clone + Send + 'static,
{
    btree: &'a BTreeSet<T>,
    index_iter: crossbeam_skiplist::map::Iter<'a, T, Arc<Mutex<Vec<T>>>>,
    current_front_entry: Option<crossbeam_skiplist::map::Entry<'a, T, Arc<Mutex<Vec<T>>>>>,
    current_front_entry_guard: Option<ArcMutexGuard<RawMutex, Vec<T>>>,
    current_front_entry_iter: Option<std::slice::Iter<'a, T>>,
    current_back_entry: Option<crossbeam_skiplist::map::Entry<'a, T, Arc<Mutex<Vec<T>>>>>,
    current_back_entry_guard: Option<ArcMutexGuard<RawMutex, Vec<T>>>,
    current_back_entry_iter: Option<std::slice::Iter<'a, T>>,
}

impl<'a, T> Iter<'a, T>
where
    T: Ord + Clone + Send + 'static,
{
    pub fn new(btree: &'a BTreeSet<T>) -> Self {
        let mut index_iter = btree.index.iter();
        let current_front_entry = index_iter.next();
        let current_front_entry_guard = if let Some(current_entry) = current_front_entry.clone() {
            Some(current_entry.value().lock_arc())
        } else {
            None
        };
        let current_front_entry_iter =
            if let Some(current_entry_iter) = current_front_entry_guard.clone() {
                Some(current_entry_iter.iter())
            } else {
                None
            };

        let current_back_entry = index_iter.next_back();

        Self {
            btree,
            index_iter,
            current_front_entry,
            current_front_entry_guard,
            current_front_entry_iter,
            current_back_entry,
        }
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
        let num_threads = 128;
        let operations_per_thread = 10000;
        let mut handles = vec![];

        let test_data: Vec<Vec<(i32, i32)>> = (0..num_threads)
            .map(|_| {
                let mut rng = rand::thread_rng();
                (0..operations_per_thread)
                    .map(|_| {
                        let value = rng.gen_range(0..100000);
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

        let n = 2048 * 100;
        let range = 0..n;
        let mut inserted_values = HashSet::new();
        for _ in range {
            let value = rng.gen_range(0..n);
            if inserted_values.insert(value) {
                assert!(set.insert(value));
            }
        }

        assert_eq!(
            set.len(),
            inserted_values.len(),
            "Length did not match, missing: {:?}",
            set.index
                .iter()
                .flat_map(|entry| entry.value().lock().iter().cloned().collect::<Vec<_>>())
                .collect::<HashSet<_>>()
                .symmetric_difference(&inserted_values)
                .collect::<Vec<_>>()
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
