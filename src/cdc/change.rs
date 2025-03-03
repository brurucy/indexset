#[cfg(feature = "multimap")]
use crate::core::multipair::MultiPair;

use crate::core::pair::Pair;

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

#[cfg(feature = "multimap")]
impl<K: Ord, V: PartialEq> From<ChangeEvent<MultiPair<K, V>>> for ChangeEvent<Pair<K, V>> {
    fn from(ev: ChangeEvent<MultiPair<K, V>>) -> Self {
        match ev {
            ChangeEvent::InsertAt {
                max_value,
                value,
                index,
            } => ChangeEvent::InsertAt {
                max_value: max_value.into(),
                value: value.into(),
                index,
            },
            ChangeEvent::RemoveAt {
                max_value,
                value,
                index,
            } => ChangeEvent::RemoveAt {
                max_value: max_value.into(),
                value: value.into(),
                index,
            },
            ChangeEvent::CreateNode { max_value } => ChangeEvent::CreateNode {
                max_value: max_value.into(),
            },
            ChangeEvent::RemoveNode { max_value } => ChangeEvent::RemoveNode {
                max_value: max_value.into(),
            },
            ChangeEvent::SplitNode {
                max_value,
                split_index,
            } => ChangeEvent::SplitNode {
                max_value: max_value.into(),
                split_index,
            },
        }
    }
}
