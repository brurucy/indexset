#[cfg(feature = "multimap")]
use crate::core::multipair::MultiPair;
#[cfg(feature = "multimap")]
use crate::core::pair::Pair;

/// Event unique identifier.
///
/// For two events `event1` and `event2` if `event1` should be applied before
/// `event2`, `event1.id()` should be less than `event2.id()`.
#[derive(Copy, Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct Id(u64);

impl Id {
    pub fn inner(&self) -> u64 {
        self.0
    }

    pub fn is_next_for(&self, other: Id) -> bool {
        self.0 == other.0 + 1
    }
}

impl From<u64> for Id {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

impl From<Id> for u64 {
    fn from(id: Id) -> Self {
        id.0
    }
}

#[derive(Debug, Clone)]
pub enum ChangeEvent<T> {
    /// Describes value insert event.
    InsertAt {
        /// `Id` of this `ChangeEvent`.
        event_id: Id,
        /// Max value that is used to identify node to remove value in.
        max_value: T,
        /// Value that is inserted itself.
        value: T,
        /// Index of a place in array to insert a value in.
        index: usize,
    },
    /// Describes value remove event.
    RemoveAt {
        /// `Id` of this `ChangeEvent`.
        event_id: Id,
        /// Max value that is used to identify node to remove value from.
        max_value: T,
        /// Value that is removed itself.
        value: T,
        /// Index of a place in array to remove a value from.
        index: usize,
    },
    /// Describes node creation event.
    CreateNode {
        /// `Id` of this `ChangeEvent`.
        event_id: Id,
        /// Initial max value.
        max_value: T,
    },
    /// Describes node removal event.
    RemoveNode {
        /// `Id` of this `ChangeEvent`.
        event_id: Id,
        /// Max value that is used to identify removed node.
        max_value: T,
    },
    /// Describes node split event.
    SplitNode {
        /// `Id` of this `ChangeEvent`.
        event_id: Id,
        /// Max value that is used to identify node to split.
        max_value: T,
        /// Index of a value that will be last value in first split part.
        split_index: usize,
    },
}

impl<T> ChangeEvent<T> {
    pub fn id(&self) -> Id {
        match self {
            ChangeEvent::InsertAt { event_id, .. } => *event_id,
            ChangeEvent::RemoveAt { event_id, .. } => *event_id,
            ChangeEvent::CreateNode { event_id, .. } => *event_id,
            ChangeEvent::RemoveNode { event_id, .. } => *event_id,
            ChangeEvent::SplitNode { event_id, .. } => *event_id,
        }
    }
}

#[cfg(feature = "multimap")]
impl<K: Ord, V: PartialEq> From<ChangeEvent<MultiPair<K, V>>> for ChangeEvent<Pair<K, V>> {
    fn from(ev: ChangeEvent<MultiPair<K, V>>) -> Self {
        match ev {
            ChangeEvent::InsertAt {
                event_id,
                max_value,
                value,
                index,
            } => ChangeEvent::InsertAt {
                event_id,
                max_value: max_value.into(),
                value: value.into(),
                index,
            },
            ChangeEvent::RemoveAt {
                event_id,
                max_value,
                value,
                index,
            } => ChangeEvent::RemoveAt {
                event_id,
                max_value: max_value.into(),
                value: value.into(),
                index,
            },
            ChangeEvent::CreateNode {
                event_id,
                max_value,
            } => ChangeEvent::CreateNode {
                event_id,
                max_value: max_value.into(),
            },
            ChangeEvent::RemoveNode {
                event_id,
                max_value,
            } => ChangeEvent::RemoveNode {
                event_id,
                max_value: max_value.into(),
            },
            ChangeEvent::SplitNode {
                event_id,
                max_value,
                split_index,
            } => ChangeEvent::SplitNode {
                event_id,
                max_value: max_value.into(),
                split_index,
            },
        }
    }
}
