use std::marker::PhantomData;
use parking_lot::{ArcMutexGuard, RawMutex};
use crate::core::node::NodeLike;

pub struct Ref<T: Ord + Clone + Send, Node: NodeLike<T> + Send> {
    pub(super) node_guard: ArcMutexGuard<RawMutex, Node>,
    pub(super) position: usize,
    pub(super) phantom_data: PhantomData<T>
}

impl<T: Ord + Clone + Send, Node: NodeLike<T> + Send> Ref<T, Node> {
    pub fn get(&self) -> &T {
        self.node_guard.get_ith(self.position).unwrap()
    }
}