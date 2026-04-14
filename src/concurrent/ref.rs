use crate::core::node::NodeLike;
use parking_lot::{ArcMutexGuard, RawMutex};
use std::marker::PhantomData;

pub struct Ref<T: Ord + Clone + Send, Node: NodeLike<T> + Send> {
    pub(super) node_guard: ArcMutexGuard<RawMutex, Node>,
    pub(super) position: usize,
    pub(super) phantom_data: PhantomData<T>,
}

impl<T: Ord + Clone + Send, Node: NodeLike<T> + Send> Ref<T, Node> {
    pub fn get(&self) -> &T {
        self.node_guard.get_ith(self.position).unwrap()
    }
}
