use std::fmt::Debug;
use std::sync::Arc;
#[cfg(feature = "cdc")]
use std::sync::atomic::{AtomicU64, Ordering};

use crossbeam_skiplist::SkipMap;
use parking_lot::{ArcMutexGuard, Mutex, RawMutex};

use crate::cdc::change::ChangeEvent;
use crate::core::node::NodeLike;

type OldVersion<Node> = Arc<Mutex<Node>>;
type CurrentVersion<Node> = Arc<Mutex<Node>>;

pub enum Operation<T: Send + Ord, Node: NodeLike<T>> {
    Split(OldVersion<Node>, T, T),
    UpdateMax(CurrentVersion<Node>, T),
    MakeUnreachable(CurrentVersion<Node>,  T),
}

impl<T, Node> Operation<T, Node>
where T: Debug + Ord + Send + Clone + 'static,
      Node: NodeLike<T> + Send + 'static,
{
    pub fn commit(self,
                  index: &SkipMap<T, Arc<Mutex<Node>>>,
                  #[cfg(feature = "cdc")] event_id: &AtomicU64,
    ) -> Result<(Option<T>, Vec<ChangeEvent<T>>), ()> {
        match self {
            Operation::Split(old_node,  old_max, value) => {
                let mut guard = old_node.lock_arc();
                if let Some(entry) = index.get(&old_max) {
                    if Arc::ptr_eq(entry.value(), &old_node) {
                        let mut cdc = vec![];
                        entry.remove();
                        let mut new_vec = guard.halve();

                        #[cfg(feature = "cdc")]
                        {
                            let node_split = ChangeEvent::SplitNode {
                                event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                max_value: old_max.clone(),
                                split_index: guard.len(),
                            };
                            cdc.push(node_split);
                        }

                        let mut old_value: Option<T> = None;
                        let mut insert_attempted = false;
                        if let Some(max) = guard.max().cloned() {
                            if max > value {
                                let (inserted, idx) = NodeLike::insert(&mut *guard, value.clone());
                                insert_attempted = true;
                                if !inserted {
                                    old_value = NodeLike::replace(&mut *guard, idx, value.clone());
                                    #[cfg(feature = "cdc")]
                                    {
                                        let value_insertion = ChangeEvent::RemoveAt {
                                            event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                            max_value: max.clone(),
                                            index: idx,
                                            value: old_value.clone().unwrap(),
                                        };
                                        cdc.push(value_insertion);
                                    }
                                }
                                #[cfg(feature = "cdc")]
                                {
                                    let value_insertion = ChangeEvent::InsertAt {
                                        event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                        max_value: max.clone(),
                                        index: idx,
                                        value: value.clone(),
                                    };
                                    cdc.push(value_insertion);
                                }
                            }

                            index.insert(max, old_node.clone());
                        }

                        if let Some(mut max) = new_vec.max().cloned() {
                            if !insert_attempted {
                                let (inserted, idx) = NodeLike::insert(&mut new_vec, value.clone());
                                let old_max = max.clone();
                                if inserted {
                                    if value > max {
                                        max = value.clone()
                                    }
                                } else {
                                    old_value = NodeLike::replace(&mut new_vec, idx, value.clone());
                                    #[cfg(feature = "cdc")]
                                    {
                                        let value_insertion = ChangeEvent::RemoveAt {
                                            event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                            max_value: old_max.clone(),
                                            index: idx,
                                            value: old_value.clone().unwrap(),
                                        };
                                        cdc.push(value_insertion);
                                    }
                                }
                                #[cfg(feature = "cdc")]
                                {
                                    let value_insertion = ChangeEvent::InsertAt {
                                        event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                        max_value: old_max.clone(),
                                        index: idx,
                                        value: value.clone(),
                                    };
                                    cdc.push(value_insertion);
                                }
                            }
                            let new_node = Arc::new(Mutex::new(new_vec));

                            index.insert(max, new_node);
                        }

                        return Ok((old_value, cdc));
                    }
                }

                Err(())
            }
            Operation::UpdateMax(node, old_max) => {
                let guard = node.lock_arc();
                let new_max = guard.max().unwrap();
                if let Some(entry) = index.get(&old_max) {
                    if Arc::ptr_eq(entry.value(), &node) {
                        let cdc = vec![];
                        return Ok(match new_max.cmp(&old_max) {
                            std::cmp::Ordering::Equal => (None, cdc),
                            std::cmp::Ordering::Greater => {
                                index.remove(&old_max);
                                index.insert(new_max.clone(), node.clone());

                                (None, cdc)
                            }
                            std::cmp::Ordering::Less => {
                                index.remove(&old_max);
                                index.insert(new_max.clone(), node.clone());

                                (None, cdc)
                            }
                        });
                    }
                }

                Err(())
            }
            Operation::MakeUnreachable(node, old_max) => {
                let guard = node.lock_arc();
                let new_max = guard.max();
                if let Some(entry) = index.get(&old_max) {
                    if Arc::ptr_eq(entry.value(), &node) {
                        return match new_max.cmp(&Some(&old_max)) {
                            std::cmp::Ordering::Less => {
                                let mut cdc = vec![];

                                #[cfg(feature = "cdc")]
                                {
                                    let node_removal = ChangeEvent::RemoveNode {
                                        event_id: event_id.fetch_add(1, Ordering::Relaxed).into(),
                                        max_value: old_max.clone(),
                                    };
                                    cdc.push(node_removal);
                                }
                                index.remove(&old_max);

                                Ok((None, cdc))
                            }
                            _ => Err(()),
                        };
                    }
                }

                Err(())
            }
        }
    }
}
