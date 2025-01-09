use parking_lot::{ArcMutexGuard, RawMutex};

pub struct Ref<T: Ord + Clone + Send> {
    pub(super) node_guard: ArcMutexGuard<RawMutex, Vec<T>>,
    pub(super) position: usize,
}

impl<T: Ord + Clone + Send> Ref<T> {
    pub fn get(&self) -> &T {
        self.node_guard.get(self.position).unwrap()
    }
}