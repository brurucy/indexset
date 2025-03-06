# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.11.1] - 2025-03-06

### Changed
- `crate::core` is now public

## [0.11.0] - 2025-03-03

### Added
- `remove_some_cdc` to `BTreeMultiMap`

### Changed
- `MultiPair` has a bijection to `Pair`

## [0.10.4] - 2025-02-15

### Fixed
- `BTreeMap::get` getting the __closest__ value instead of the __exact__ value

## [0.10.3] - 2025-01-27

### Changed
- Made `pair`, `node`, `multipair` and `constants` public

## [0.10.2] - 2025-01-11

### Changed
- Improved the README.

## [0.10.1] - 2025-01-11

### Fixed
- Some edge cases in `concurrent::set::Range`

## [0.10.0] - 2025-01-09

### Added
- `BTreeMultiMap`, a concurrent BTree that allows multiple values per key.

## [0.9.0] - 2025-01-04

### Changed
- `CDC` API now does not return clones of Nodes anymore, instead returning __where__ to insert and remove elements.

## [0.8.1] - 2025-01-03

### Added
- Add docs.rs coverage for opt-in feats

## [0.8.0] - 2024-12-29

### Fixed
- erroneously returning false even when insertion was correct in `concurrent::{set, map}`.

### Added
- `range` method to `concurrent::map::BTreeMap`

## [0.7.1] - 2024-12-27

### Fixed
- `concurrent` feature works without `cdc` being enabled.

## [0.7.0] - 2024-12-22

### Added
- CDC feature. If toggled on, returns the change events associated with the mutating operation.
- `with_maximum_node_size` method for `BTreeSet` and `BTreeMap`

## [0.6.1] - 2024-12-20

### Fixed
- `remove` method for concurrent `BTreeSet` and `BTreeMap` does not need a mutable reference.

## [0.6.0] - 2024-12-19

### Added
- A benchmark for concurrent implementations

### Changed
- A new **much faster** partially lock free concurrent implementation 
- Reorganized the library

## [0.5.0] - 2024-09-18

### Added

- Concurrent implementations

## [0.4.1] - 2024-08-19

### Fixed

- Inconsistent index after many duplicated items are inserted thanks to @michaelsutton

## [0.4.0] - 2024-05-24

### Added

- Implementations of `PartialEq`, `Eq`, `Ord`, `Hash` for `BTreeSet` and `BTreeMap`

### Changed

- Bumped `ftree` crate

### Removed

- Requirement for `T` to implement `Clone`

## [0.3.8] - 2024-02-18

### Changed

- Bumped `ftree` crate

## [0.3.7] - 2024-02-18

### Fixed

- Many overflows relating to range bounds thanks to @Cydhra

## [0.3.6] - 2023-08-12

### Changed

- solved many clippy warnings
- added a custom binary search with fixed iteration bound

## [0.3.5] - 2023-07-17

### Added

- new `with_maximum_node_size` method for `BTreeSet` and `BTreeMap`

## [0.3.4] - 2023-07-14

### Changed

- upgraded `ftree` to 1.0.0

## [0.3.3] - 2023-07-13

### Changed

- normalized naming across the code

### Added

- exposed the `rank` function in `BTreeSet` and `BTreeMap`

## [0.3.2] - 2023-07-12

### Changed

- moved `FenwickTree` to another crate
- simplified structure

## [0.3.1] - 2023-07-10

### Changed

- reworked the internals of `insert`
- removed dead code

## [0.3.0] - 2023-07-10

### Added

- `lower_bound` providing initial `Cursor` support for `BTreeMap`

## [0.2.0] - 2023-07-09

### Added

- `Entry` API for `BTreeMap`
- `serde` feature for deserialization of `BTreeSet` and `BTreeMap`

## [0.1.0] - 2023-07-04

### Added

- `BTreeSet`
- `BTreeMap`

[Unreleased]: https://github.com/brurucy/indexset/compare/v0.11.1...HEAD

[0.11.1]: https://github.com/brurucy/indexset/releases/tag/v0.11.1

[0.11.0]: https://github.com/brurucy/indexset/releases/tag/v0.11.0

[0.10.4]: https://github.com/brurucy/indexset/releases/tag/v0.10.4

[0.10.3]: https://github.com/brurucy/indexset/releases/tag/v0.10.3

[0.10.2]: https://github.com/brurucy/indexset/releases/tag/v0.10.2

[0.10.1]: https://github.com/brurucy/indexset/releases/tag/v0.10.1

[0.10.0]: https://github.com/brurucy/indexset/releases/tag/v0.10.0

[0.9.0]: https://github.com/brurucy/indexset/releases/tag/v0.9.0

[0.8.1]: https://github.com/brurucy/indexset/releases/tag/v0.8.1

[0.8.0]: https://github.com/brurucy/indexset/releases/tag/v0.8.0

[0.7.1]: https://github.com/brurucy/indexset/releases/tag/v0.7.1

[0.7.0]: https://github.com/brurucy/indexset/releases/tag/v0.7.0

[0.6.1]: https://github.com/brurucy/indexset/releases/tag/v0.6.1

[0.6.0]: https://github.com/brurucy/indexset/releases/tag/v0.6.0

[0.5.0]: https://github.com/brurucy/indexset/releases/tag/v0.5.0

[0.4.1]: https://github.com/brurucy/indexset/releases/tag/v0.4.1

[0.4.0]: https://github.com/brurucy/indexset/releases/tag/v0.4.0

[0.3.8]: https://github.com/brurucy/indexset/releases/tag/v0.3.8

[0.3.7]: https://github.com/brurucy/indexset/releases/tag/v0.3.7

[0.3.6]: https://github.com/brurucy/indexset/releases/tag/v0.3.6

[0.3.5]: https://github.com/brurucy/indexset/releases/tag/v0.3.5

[0.3.4]: https://github.com/brurucy/indexset/releases/tag/v0.3.4

[0.3.3]: https://github.com/brurucy/indexset/releases/tag/v0.3.3

[0.3.2]: https://github.com/brurucy/indexset/releases/tag/v0.3.2

[0.3.1]: https://github.com/brurucy/indexset/releases/tag/v0.3.1

[0.3.0]: https://github.com/brurucy/indexset/releases/tag/v0.3.0

[0.2.0]: https://github.com/brurucy/indexset/releases/tag/v0.2.0

[0.1.0]: https://github.com/brurucy/indexset/releases/tag/v0.1.0
