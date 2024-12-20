# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.6.1] - 2024-12-20

### Fixed
- `remove` for `concurrent::*` structures does not require a mutable reference.

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

[Unreleased]: https://github.com/brurucy/indexset/compare/v0.5.0...HEAD

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
