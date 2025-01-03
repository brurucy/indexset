pub enum ChangeEvent<T> {
    InsertAt {
        max_value: T,
        value: T,
        index: usize,
    },
    RemoveAt {
        max_value: T,
        value: T,
        index: usize,
    },
    InsertNode {
        max_value: T,
        node: crate::concurrent::set::Node<T>,
    },
    RemoveNode {
        max_value: T,
    },
}
