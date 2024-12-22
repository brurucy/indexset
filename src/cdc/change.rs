pub enum ChangeEvent<T> {
    InsertAt(T, T),
    RemoveAt(T, T),
    InsertNode(T, crate::concurrent::set::Node<T>),
    RemoveNode(T),
}
