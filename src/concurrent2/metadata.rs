#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Dimension {
    pub num_entries: usize,
    pub num_bits_per_entry: usize,
}

impl Dimension {
    /// Checks if the [`Leaf`] is frozen.
    pub(crate) const fn frozen(metadata: usize) -> bool {
        metadata & (1_usize << (usize::BITS - 2)) != 0
    }

    /// Makes the metadata represent a frozen state.
    pub(crate) const fn freeze(metadata: usize) -> usize {
        metadata | (1_usize << (usize::BITS - 2))
    }

    /// Updates the metadata to represent a non-frozen state.
    pub(crate) const fn thaw(metadata: usize) -> usize {
        metadata & (!(1_usize << (usize::BITS - 2)))
    }

    /// Checks if the [`Leaf`] is retired.
    pub(crate) const fn retired(metadata: usize) -> bool {
        metadata & (1_usize << (usize::BITS - 1)) != 0
    }

    /// Makes the metadata represent a retired state.
    pub(crate) const fn retire(metadata: usize) -> usize {
        metadata | (1_usize << (usize::BITS - 1))
    }

    /// Returns a bit mask for an entry.
    pub(crate) const fn rank_mask(&self, index: usize) -> usize {
        ((1_usize << self.num_bits_per_entry) - 1) << (index * self.num_bits_per_entry)
    }

    /// Returns the rank of an entry.
    pub(crate) const fn rank(&self, metadata: usize, index: usize) -> usize {
        (metadata >> (index * self.num_bits_per_entry)) % (1_usize << self.num_bits_per_entry)
    }

    /// Returns the uninitialized rank value which is smaller than all the valid rank values.
    pub(crate) const fn uninit_rank() -> usize {
        0
    }

    /// Returns the removed rank value which is greater than all the valid rank values.
    pub(crate) const fn removed_rank(&self) -> usize {
        (1_usize << self.num_bits_per_entry) - 1
    }

    /// Augments the rank to the given metadata.
    pub(crate) const fn augment(&self, metadata: usize, index: usize, rank: usize) -> usize {
        (metadata & (!self.rank_mask(index))) | (rank << (index * self.num_bits_per_entry))
    }
}

impl Dimension {
    const fn to_bytes(val: usize) -> [u8; 8] {
        [
            (val & 0xFF) as u8,
            ((val >> 8) & 0xFF) as u8,
            ((val >> 16) & 0xFF) as u8,
            ((val >> 24) & 0xFF) as u8,
            ((val >> 32) & 0xFF) as u8,
            ((val >> 40) & 0xFF) as u8,
            ((val >> 48) & 0xFF) as u8,
            ((val >> 56) & 0xFF) as u8,
        ]
    }

    const fn from_bytes(bytes: [u8; 8]) -> usize {
        let mut result = 0usize;
        result |= (bytes[7] as usize) << 56;
        result |= (bytes[6] as usize) << 48;
        result |= (bytes[5] as usize) << 40;
        result |= (bytes[4] as usize) << 32;
        result |= (bytes[3] as usize) << 24;
        result |= (bytes[2] as usize) << 16;
        result |= (bytes[1] as usize) << 8;
        result |= bytes[0] as usize;
        result
    }

    pub(crate) const fn frozen_bytes(metadata: [u8; 8]) -> bool {
        // Check second-to-highest bit (bit 62) in the last byte
        metadata[7] & 0b0100_0000 != 0
    }

    pub(crate) const fn freeze_bytes(mut metadata: [u8; 8]) -> [u8; 8] {
        // Set second-to-highest bit (bit 62) in the last byte
        metadata[7] |= 0b0100_0000;
        metadata
    }

    pub(crate) const fn thaw_bytes(mut metadata: [u8; 8]) -> [u8; 8] {
        // Clear second-to-highest bit (bit 62) in the last byte
        metadata[7] &= !0b0100_0000;
        metadata
    }

    pub(crate) const fn retired_bytes(metadata: [u8; 8]) -> bool {
        // Check highest bit (bit 63) in the last byte
        metadata[7] & 0b1000_0000 != 0
    }

    pub(crate) const fn retire_bytes(mut metadata: [u8; 8]) -> [u8; 8] {
        // Set highest bit (bit 63) in the last byte
        metadata[7] |= 0b1000_0000;
        metadata
    }

    pub(crate) const fn rank_mask_bytes(&self, index: usize) -> [u8; 8] {
        let mut result = [0u8; 8];
        let start_bit = index * self.num_bits_per_entry;
        let end_bit = start_bit + self.num_bits_per_entry;

        let mut current_bit = start_bit;
        while current_bit < end_bit {
            let byte_idx = current_bit / 8;
            let bit_pos = current_bit % 8;
            result[byte_idx] |= 1 << bit_pos;
            current_bit += 1;
        }
        result
    }

    pub(crate) const fn rank_bytes(&self, metadata: [u8; 8], index: usize) -> usize {
        let start_bit = index * self.num_bits_per_entry;
        let mut result = 0usize;
        let mut bit_count = 0;

        while bit_count < self.num_bits_per_entry {
            let global_bit = start_bit + bit_count;
            let byte_idx = global_bit / 8;
            let bit_pos = global_bit % 8;

            if metadata[byte_idx] & (1 << bit_pos) != 0 {
                result |= 1 << bit_count;
            }
            bit_count += 1;
        }
        result
    }

    pub(crate) const fn uninit_rank_bytes() -> [u8; 8] {
        [0u8; 8]
    }

    pub(crate) const fn removed_rank_bytes(&self) -> [u8; 8] {
        let mut result = [0u8; 8];
        let mut bit_count = 0;

        while bit_count < self.num_bits_per_entry {
            let byte_idx = bit_count / 8;
            let bit_pos = bit_count % 8;
            result[byte_idx] |= 1 << bit_pos;
            bit_count += 1;
        }
        result
    }

    pub(crate) const fn augment_bytes(
        &self,
        mut metadata: [u8; 8],
        index: usize,
        rank: usize,
    ) -> [u8; 8] {
        let start_bit = index * self.num_bits_per_entry;

        // Clear the bits for this rank
        let mut bit_count = 0;
        while bit_count < self.num_bits_per_entry {
            let global_bit = start_bit + bit_count;
            let byte_idx = global_bit / 8;
            let bit_pos = global_bit % 8;
            metadata[byte_idx] &= !(1 << bit_pos);
            bit_count += 1;
        }

        // Set the new rank bits
        let mut bit_count = 0;
        while bit_count < self.num_bits_per_entry {
            let global_bit = start_bit + bit_count;
            let byte_idx = global_bit / 8;
            let bit_pos = global_bit % 8;

            if (rank & (1 << bit_count)) != 0 {
                metadata[byte_idx] |= 1 << bit_pos;
            }
            bit_count += 1;
        }

        metadata
    }
}

/// The maximum number of entries and the number of metadata bits per entry in a [`Leaf`].
///
/// * `M`: The maximum number of entries.
/// * `B`: The minimum number of bits to express the state of an entry.
/// * `2`: The number of special states of an entry: uninitialized, removed.
/// * `2`: The number of special states of a [`Leaf`]: frozen, retired.
/// * `U`: `usize::BITS`.
/// * `Eq1 = M + 2 <= 2^B`: `B` bits represent at least `M + 2` states.
/// * `Eq2 = B * M + 2 <= U`: `M entries + 2` special state.
/// * `Eq3 = Ceil(Log2(M + 2)) * M + 2 <= U`: derived from `Eq1` and `Eq2`.
///
/// Therefore, when `U = 64 => M = 14 / B = 4`, and `U = 32 => M = 7 / B = 4`.
pub const DIMENSION: Dimension = match usize::BITS / 8 {
    1 => Dimension {
        num_entries: 2,
        num_bits_per_entry: 2,
    },
    2 => Dimension {
        num_entries: 4,
        num_bits_per_entry: 3,
    },
    4 => Dimension {
        num_entries: 7,
        num_bits_per_entry: 4,
    },
    8 => Dimension {
        num_entries: 14,
        num_bits_per_entry: 4,
    },
    _ => Dimension {
        num_entries: 25,
        num_bits_per_entry: 5,
    },
};

mod tests {
    use super::*;

    const TEST_DIMENSION: Dimension = Dimension {
        num_entries: 14,
        num_bits_per_entry: 4,
    };

    #[test]
    fn test_conversion_roundtrip() {
        let original = 0xDEADBEEFCAFEBABEu64 as usize;
        let bytes = Dimension::to_bytes(original);
        let recovered = Dimension::from_bytes(bytes);
        assert_eq!(original, recovered, "Value changed during byte conversion");
    }

    #[test]
    fn test_frozen() {
        let normal = 0usize;
        let normal_bytes = Dimension::to_bytes(normal);

        // Test initial state
        assert!(!Dimension::frozen(normal));
        assert!(!Dimension::frozen_bytes(normal_bytes));

        // Test freezing
        let frozen = Dimension::freeze(normal);
        let frozen_bytes = Dimension::freeze_bytes(normal_bytes);
        assert!(Dimension::frozen(frozen));
        assert!(Dimension::frozen_bytes(frozen_bytes));
        assert_eq!(Dimension::from_bytes(frozen_bytes), frozen);

        // Test thawing
        let thawed = Dimension::thaw(frozen);
        let thawed_bytes = Dimension::thaw_bytes(frozen_bytes);
        assert!(!Dimension::frozen(thawed));
        assert!(!Dimension::frozen_bytes(thawed_bytes));
        assert_eq!(Dimension::from_bytes(thawed_bytes), thawed);
    }

    #[test]
    fn test_retired() {
        let normal = 0usize;
        let normal_bytes = Dimension::to_bytes(normal);

        // Test initial state
        assert!(!Dimension::retired(normal));
        assert!(!Dimension::retired_bytes(normal_bytes));

        // Test retiring
        let retired = Dimension::retire(normal);
        let retired_bytes = Dimension::retire_bytes(normal_bytes);
        assert!(Dimension::retired(retired));
        assert!(Dimension::retired_bytes(retired_bytes));
        assert_eq!(Dimension::from_bytes(retired_bytes), retired);
    }

    #[test]
    fn test_rank_operations() {
        let dim = TEST_DIMENSION;
        let initial = 0usize;
        let initial_bytes = Dimension::to_bytes(initial);

        // Test rank mask
        let mask = dim.rank_mask(0);
        let mask_bytes = dim.rank_mask_bytes(0);
        assert_eq!(Dimension::from_bytes(mask_bytes), mask);
        assert_eq!(mask, 0b1111); // For 4 bits

        // Test setting and getting rank
        let with_rank = dim.augment(initial, 0, 5);
        let with_rank_bytes = dim.augment_bytes(initial_bytes, 0, 5);
        assert_eq!(dim.rank(with_rank, 0), 5);
        assert_eq!(dim.rank_bytes(with_rank_bytes, 0), 5);
        assert_eq!(Dimension::from_bytes(with_rank_bytes), with_rank);

        // Test multiple ranks don't interfere
        let with_multiple = dim.augment(with_rank, 1, 7);
        let with_multiple_bytes = dim.augment_bytes(with_rank_bytes, 1, 7);
        assert_eq!(dim.rank(with_multiple, 0), 5);
        assert_eq!(dim.rank(with_multiple, 1), 7);
        assert_eq!(dim.rank_bytes(with_multiple_bytes, 0), 5);
        assert_eq!(dim.rank_bytes(with_multiple_bytes, 1), 7);
    }

    #[test]
    fn test_special_ranks() {
        let dim = TEST_DIMENSION;

        // Test uninit rank
        let uninit = Dimension::uninit_rank();
        let uninit_bytes = Dimension::uninit_rank_bytes();
        assert_eq!(uninit, 0);
        assert_eq!(Dimension::from_bytes(uninit_bytes), uninit);

        // Test removed rank
        let removed = dim.removed_rank();
        let removed_bytes = dim.removed_rank_bytes();
        assert_eq!(removed, (1 << dim.num_bits_per_entry) - 1);
        assert_eq!(Dimension::from_bytes(removed_bytes), removed);
    }

    #[test]
    fn test_combined_states() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = Dimension::to_bytes(metadata);

        // Test frozen + retired combination
        metadata = Dimension::freeze(metadata);
        metadata = Dimension::retire(metadata);
        metadata_bytes = Dimension::freeze_bytes(metadata_bytes);
        metadata_bytes = Dimension::retire_bytes(metadata_bytes);

        assert!(Dimension::frozen(metadata));
        assert!(Dimension::retired(metadata));
        assert!(Dimension::frozen_bytes(metadata_bytes));
        assert!(Dimension::retired_bytes(metadata_bytes));
        assert_eq!(Dimension::from_bytes(metadata_bytes), metadata);

        // Test ranks with state flags
        metadata = dim.augment(metadata, 0, 5);
        metadata_bytes = dim.augment_bytes(metadata_bytes, 0, 5);

        assert_eq!(dim.rank(metadata, 0), 5);
        assert_eq!(dim.rank_bytes(metadata_bytes, 0), 5);
        assert!(Dimension::frozen(metadata));
        assert!(Dimension::retired(metadata));
        assert!(Dimension::frozen_bytes(metadata_bytes));
        assert!(Dimension::retired_bytes(metadata_bytes));
    }

    #[test]
    fn test_rank_bounds() {
        let dim = TEST_DIMENSION;
        let metadata = 0usize;
        let metadata_bytes = Dimension::to_bytes(metadata);

        // Test maximum valid rank
        let max_rank = (1 << dim.num_bits_per_entry) - 1;
        let with_max = dim.augment(metadata, 0, max_rank);
        let with_max_bytes = dim.augment_bytes(metadata_bytes, 0, max_rank);

        assert_eq!(dim.rank(with_max, 0), max_rank);
        assert_eq!(dim.rank_bytes(with_max_bytes, 0), max_rank);

        // Test last entry position
        let last_index = dim.num_entries - 1;
        let with_last = dim.augment(metadata, last_index, 5);
        let with_last_bytes = dim.augment_bytes(metadata_bytes, last_index, 5);

        assert_eq!(dim.rank(with_last, last_index), 5);
        assert_eq!(dim.rank_bytes(with_last_bytes, last_index), 5);
    }

    #[test]
    fn test_all_bits_set() {
        let dim = TEST_DIMENSION;
        let all_ones = usize::MAX;
        let all_ones_bytes = [0xFF; 8];

        // Check state flags
        assert!(Dimension::frozen(all_ones));
        assert!(Dimension::retired(all_ones));
        assert!(Dimension::frozen_bytes(all_ones_bytes));
        assert!(Dimension::retired_bytes(all_ones_bytes));

        // Check ranks
        for i in 0..dim.num_entries {
            assert_eq!(dim.rank(all_ones, i), (1 << dim.num_bits_per_entry) - 1);
            assert_eq!(
                dim.rank_bytes(all_ones_bytes, i),
                (1 << dim.num_bits_per_entry) - 1
            );
        }
    }

    #[test]
    fn test_alternating_bits() {
        let dim = TEST_DIMENSION;
        let alternating = 0xAAAAAAAAAAAAAAAA;
        let alternating_bytes = Dimension::to_bytes(alternating);

        // Test ranks with alternating bits
        for i in 0..dim.num_entries {
            let rank = dim.rank(alternating, i);
            let rank_bytes = dim.rank_bytes(alternating_bytes, i);
            assert_eq!(rank, rank_bytes);
        }
    }

    #[test]
    fn test_rank_overflow_patterns() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Set all ranks to maximum value
        for i in 0..dim.num_entries {
            let max_rank = (1 << dim.num_bits_per_entry) - 1;
            metadata = dim.augment(metadata, i, max_rank);
            metadata_bytes = dim.augment_bytes(metadata_bytes, i, max_rank);
        }

        // Verify all ranks
        for i in 0..dim.num_entries {
            assert_eq!(dim.rank(metadata, i), dim.rank_bytes(metadata_bytes, i));
        }
    }

    #[test]
    fn test_adjacent_entries() {
        let dim = TEST_DIMENSION;
        let metadata = 0usize;
        let metadata_bytes = [0u8; 8];

        // Set adjacent entries to different values
        let with_adjacent = dim.augment(
            dim.augment(metadata, 0, (1 << dim.num_bits_per_entry) - 1),
            1,
            0,
        );
        let with_adjacent_bytes = dim.augment_bytes(
            dim.augment_bytes(metadata_bytes, 0, (1 << dim.num_bits_per_entry) - 1),
            1,
            0,
        );

        assert_eq!(
            dim.rank(with_adjacent, 0),
            (1 << dim.num_bits_per_entry) - 1
        );
        assert_eq!(dim.rank(with_adjacent, 1), 0);
        assert_eq!(
            dim.rank_bytes(with_adjacent_bytes, 0),
            (1 << dim.num_bits_per_entry) - 1
        );
        assert_eq!(dim.rank_bytes(with_adjacent_bytes, 1), 0);
    }

    #[test]
    fn test_byte_boundary_ranks() {
        let dim = Dimension {
            num_entries: 16,
            num_bits_per_entry: 12, // This will cause ranks to cross byte boundaries
        };

        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Set values that cross byte boundaries
        let test_ranks = [0xFFF, 0x555, 0xAAA, 0x111];
        for (i, &rank) in test_ranks.iter().enumerate() {
            metadata = dim.augment(metadata, i, rank);
            metadata_bytes = dim.augment_bytes(metadata_bytes, i, rank);
        }

        // Verify values
        for (i, &rank) in test_ranks.iter().enumerate() {
            assert_eq!(dim.rank(metadata, i), rank);
            assert_eq!(dim.rank_bytes(metadata_bytes, i), rank);
        }
    }

    #[test]
    fn test_state_preservation() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Set both state flags
        metadata = Dimension::freeze(metadata);
        metadata = Dimension::retire(metadata);
        metadata_bytes = Dimension::freeze_bytes(metadata_bytes);
        metadata_bytes = Dimension::retire_bytes(metadata_bytes);

        // Modify ranks and verify states are preserved
        for i in 0..dim.num_entries {
            metadata = dim.augment(metadata, i, i);
            metadata_bytes = dim.augment_bytes(metadata_bytes, i, i);

            // Verify states after each modification
            assert!(Dimension::frozen(metadata));
            assert!(Dimension::retired(metadata));
            assert!(Dimension::frozen_bytes(metadata_bytes));
            assert!(Dimension::retired_bytes(metadata_bytes));
        }
    }

    #[test]
    fn test_rank_patterns() {
        let dim = TEST_DIMENSION;
        let patterns = [
            0x0000_0000_0000_0000,
            0xFFFF_FFFF_FFFF_FFFF,
            0x5555_5555_5555_5555,
            0xAAAA_AAAA_AAAA_AAAA,
            0x1111_1111_1111_1111,
            0xFFFF_0000_FFFF_0000,
            0x0000_FFFF_0000_FFFF,
        ];

        for &pattern in &patterns {
            let metadata = pattern;
            let metadata_bytes = Dimension::to_bytes(pattern);

            // Test all positions with each pattern
            for i in 0..dim.num_entries {
                assert_eq!(
                    dim.rank(metadata, i),
                    dim.rank_bytes(metadata_bytes, i),
                    "Pattern {:x} failed at position {}",
                    pattern,
                    i
                );
            }
        }
    }

    #[test]
    fn test_concurrent_operations() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Interleave operations
        metadata = Dimension::freeze(metadata);
        metadata_bytes = Dimension::freeze_bytes(metadata_bytes);

        metadata = dim.augment(metadata, 0, 5);
        metadata_bytes = dim.augment_bytes(metadata_bytes, 0, 5);

        metadata = Dimension::retire(metadata);
        metadata_bytes = Dimension::retire_bytes(metadata_bytes);

        metadata = dim.augment(metadata, 1, 7);
        metadata_bytes = dim.augment_bytes(metadata_bytes, 1, 7);

        metadata = Dimension::thaw(metadata);
        metadata_bytes = Dimension::thaw_bytes(metadata_bytes);

        // Verify final state
        assert!(!Dimension::frozen(metadata));
        assert!(Dimension::retired(metadata));
        assert_eq!(dim.rank(metadata, 0), 5);
        assert_eq!(dim.rank(metadata, 1), 7);

        assert!(!Dimension::frozen_bytes(metadata_bytes));
        assert!(Dimension::retired_bytes(metadata_bytes));
        assert_eq!(dim.rank_bytes(metadata_bytes, 0), 5);
        assert_eq!(dim.rank_bytes(metadata_bytes, 1), 7);
    }

    #[test]
    fn test_rank_bit_order() {
        let dim = TEST_DIMENSION;

        // Test asymmetric patterns that would expose reversal
        let test_cases = [
            (0b1000, "0b1000"), // Single high bit
            (0b0001, "0b0001"), // Single low bit
            (0b1010, "0b1010"), // Alternating starting high
            (0b0101, "0b0101"), // Alternating starting low
            (0b1100, "0b1100"), // High pair
            (0b0011, "0b0011"), // Low pair
            (0b1110, "0b1110"), // Three high bits
            (0b0111, "0b0111"), // Three low bits
        ];

        for (index, offset) in [(0, 0), (1, 4), (7, 28), (13, 52)].iter() {
            // Test at start, first boundary cross, middle, and end positions
            for (value, pattern) in test_cases.iter() {
                let mut metadata = 0usize;
                metadata = dim.augment(metadata, *index, *value);
                let metadata_bytes = dim.augment_bytes([0u8; 8], *index, *value);

                assert_eq!(
                    dim.rank(metadata, *index),
                    dim.rank_bytes(metadata_bytes, *index),
                    "Bit pattern {} at index {} (offset {} bits) gave different results\n\
                 usize version: {:04b}\n\
                 bytes version: {:04b}",
                    pattern,
                    index,
                    offset,
                    dim.rank(metadata, *index),
                    dim.rank_bytes(metadata_bytes, *index)
                );
            }
        }
    }

    #[test]
    fn test_byte_boundary_crossing() {
        let dim = TEST_DIMENSION;

        // Test ranks that cross byte boundaries (index 1 spans bytes 0-1)
        let value = 0b1010; // Will become split across bytes
        let mut metadata = 0usize;
        metadata = dim.augment(metadata, 1, value);
        let metadata_bytes = dim.augment_bytes([0u8; 8], 1, value);

        assert_eq!(
            dim.rank(metadata, 1),
            dim.rank_bytes(metadata_bytes, 1),
            "Rank spanning byte boundary gave different results"
        );
    }

    #[test]
    fn test_multi_rank_interactions() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Fill with alternating patterns that would expose bit reversal
        let patterns = [
            (0, 0b1010),
            (1, 0b0101),
            (2, 0b1100),
            (3, 0b0011),
            (4, 0b1110),
            (5, 0b0111),
            (6, 0b1000),
            (7, 0b0001),
        ];

        // Set all patterns
        for &(index, value) in patterns.iter() {
            metadata = dim.augment(metadata, index, value);
            metadata_bytes = dim.augment_bytes(metadata_bytes, index, value);
        }

        // Verify each pattern
        for &(index, expected) in patterns.iter() {
            assert_eq!(
                dim.rank(metadata, index),
                dim.rank_bytes(metadata_bytes, index),
                "At index {}, patterns interfered:\n\
             usize version: {:04b}\n\
             bytes version: {:04b}",
                index,
                dim.rank(metadata, index),
                dim.rank_bytes(metadata_bytes, index)
            );
        }
    }

    #[test]
    fn test_rank_with_state_flags() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Set state flags first
        metadata = Dimension::freeze(metadata);
        metadata = Dimension::retire(metadata);
        metadata_bytes = Dimension::freeze_bytes(metadata_bytes);
        metadata_bytes = Dimension::retire_bytes(metadata_bytes);

        // Now set a rank that would expose bit reversal
        let test_index = 13; // Last position, closest to flags
        let test_value = 0b1010;

        metadata = dim.augment(metadata, test_index, test_value);
        metadata_bytes = dim.augment_bytes(metadata_bytes, test_index, test_value);

        // Check state flags remained
        assert_eq!(
            Dimension::frozen(metadata),
            Dimension::frozen_bytes(metadata_bytes),
            "Frozen state mismatch after rank set"
        );
        assert_eq!(
            Dimension::retired(metadata),
            Dimension::retired_bytes(metadata_bytes),
            "Retired state mismatch after rank set"
        );

        // Check rank value
        assert_eq!(
            dim.rank(metadata, test_index),
            dim.rank_bytes(metadata_bytes, test_index),
            "Rank near flags gave different results:\n\
         usize version: {:04b}\n\
         bytes version: {:04b}",
            dim.rank(metadata, test_index),
            dim.rank_bytes(metadata_bytes, test_index)
        );
    }

    #[test]
    fn test_rank_modification_sequence() {
        let dim = TEST_DIMENSION;
        let mut metadata = 0usize;
        let mut metadata_bytes = [0u8; 8];

        // Test sequence of modifications at the same index
        let test_index = 1; // Position that crosses byte boundary
        let modifications = [
            0b1010, // Initial value
            0b0101, // Flip all bits
            0b1100, // Change to high pair
            0b0011, // Change to low pair
            0b1010, // Back to initial
        ];

        for &value in modifications.iter() {
            metadata = dim.augment(metadata, test_index, value);
            metadata_bytes = dim.augment_bytes(metadata_bytes, test_index, value);

            assert_eq!(
                dim.rank(metadata, test_index),
                dim.rank_bytes(metadata_bytes, test_index),
                "After setting {:04b}:\n\
             usize version: {:04b}\n\
             bytes version: {:04b}",
                value,
                dim.rank(metadata, test_index),
                dim.rank_bytes(metadata_bytes, test_index)
            );
        }
    }
}
