pub enum ChangeEvent<T> {
    /// Describes value insert event.
    InsertAt {
        /// Max value that is used to identify node to remove value in.
        max_value: T,
        /// Value that is inserted itself.
        value: T,
        /// Index of a place in array to insert a value in.
        index: usize,
    },
    /// Describes value remove event.
    RemoveAt {
        /// Max value that is used to identify node to remove value from.
        max_value: T,
        /// Value that is removed itself.
        value: T,
        /// Index of a place in array to remove a value from.
        index: usize,
    },
    /// Describes node creation event.
    CreateNode {
        /// Initial max value.
        max_value: T,
    },
    /// Describes node removal event.
    RemoveNode {
        /// Max value that is used to identify removed node.
        max_value: T,
    },
    /// Describes node split event.
    SplitNode {
        /// Max value that is used to identify node to split.
        max_value: T,
        /// Index of a value that will be last value in first split part.
        split_index: usize,
    },
}
