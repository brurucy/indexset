# indexset

[![crates.io](https://img.shields.io/crates/v/indexset.svg)](https://crates.io/crates/indexset)
[![docs](https://docs.rs/indexset/badge.svg)](https://docs.rs/indexset)

A pure-Rust two-level dynamic order-statistic b-tree.

This crate implements a compact set data structure that preserves its elements' sorted order and
allows lookups of entries by value or sorted order position.

Under the feature `concurrent` you can find a version of the BTree that can be fearlessly shared between
threads.

Both the concurrent and single-threaded versions are meant to be drop-in replacements for the stdlib BTree. This 
is mostly true for the latter but not for the former, yet.

The following table describes the variants of this data structure that are available:

| Variant                                    | tl;dr                                                     | Stability |
|--------------------------------------------|-----------------------------------------------------------|-----------|
| crate::BTreeSet                            | A single-threaded ordered set                             | Stable    |
| crate::BTreeMap                            | A single-threaded ordered map                             | Stable    |
| crate::concurrent::set::BTreeSet           | A concurrent ordered set                                  | Beta      |
| crate::concurrent::map::BTreeMap           | A concurrent ordered map                                  | Beta      |
| crate::concurrent::multimap::BTreeMultiMap | A concurrent ordered map where keys need not to be unique | Alpha     |

## Features

* `serde`: implements serialization and deserialization traits for the single-threaded trees 
* `concurrent`: enables the three concurrent variants of `BTreeSet` referenced in the table above
* `cdc`: provides helper methods to persist all concurrent trees
* `multimap`: enables `BTreeMultiMap`

# Background

This was heavily inspired by [`indexmap`](https://crates.io/crates/indexmap), and
python's [`sortedcontainers`](https://github.com/grantjenks/python-sortedcontainers).

It differs from both in that:

* `indexmap` is a hashmap that provides numerical lookups, but does not maintain order in case of removals, while
  `indexset`'s core data structure is a b-tree that irrespective of which mutating operation is run, always maintains order.
* `sortecontainers` is similar in spirit, but utilizes a different routine for balancing the tree, and relies
  on a heap for numerical lookups.

`indexset` provides the following features:

- As fast to iterate as a vec.
- Zero indirection.
- Lookups by position and range.
- Minimal amount of allocations.
- `select`(lookups by position) and `rank` operations in near constant time (not yet in the concurrent versions).

# Performance

`BTreeSet` and `BTreeMap` derive their performance much from how they are constructed, which is:

> A two-level B-Tree with a fenwick tree as a low-cost index for numerical lookups

Each node is a leaf, and each leaf is a vec with a fixed capacity of size `B`, with `1024` being the default.

The following hold:
- Iteration is very fast since it is done by inheriting vec's iter struct.
- Lookups only need two binary searches. One over `n/B` nodes and another over `B` elements: `O(log(n/B) + log(B)) = O(log(n))`.
- Insertions are constant time `O(B)` in the best case and `O(B^2)` in the worst. Removals are `O(log(n))`.

## Benchmarks

The following numbers were obtained on a M3 macbook pro:

### Single-threaded

Command: `cargo bench --bench stdlib --all-features`

* Inserting 100k random usize
  * `stdlib::collections::BTreeSet.insert(i)`: 8.9ms
  * `indexset::BTreeSet.insert(i)`: 13.1ms
  * `indexset::concurrent::set::BTreeSet.insert(i)`: 14.0ms
* Checking that each 100k random usize integers exist
  * `stdlib::collections::BTreeSet.contains(i)`: 7.02ms
  * `indexset::BTreeSet.contains(i)`: 5.22ms
  * `indexset::concurrent::set::BTreeSet.contains(i)`: 5.27ms
* Getting all 100k i-th elements
  * `stdlib::collections::BTreeSet.iter.nth(i)`: **13.28s** yes, seconds! 
  * `indexset::BTreeSet.get_index(i)`: **3.93ms**
* Iterating over all 100k elements and then collecting it into a vec
  * `Vec::from_iter(stdlib::collections::BTreeSet.iter())`: **227.28us**
  * `Vec::from_iter(indexset::BTreeSet.iter())`: **123.21.us**

Getting the i-th element is **3400x** faster than stdlib's btree, `contains` is 25% faster, and iterating is twice 
as fast, at the cost of insertions being 30% slower.

If your use case of `std::collections::BTreeSet` and `BTreeMap` is read-heavy, or if you really need to index by
sorted-order position, it might be worth checking out `indexset` instead.

### Concurrent

Command: `cargo bench --bench concurrent --all-features`

We benchmark concurrent operations with 40 threads, each conducting 100000 operations
at the same time that vary from a ratio of 1% writes/reads to 50% writes/reads.

In this benchmark threads have high locality and tend to focus on specific parts of the data.

* 1% writes/99% reads:
  * `indexset::concurrent::set::BTreeSet`: 170.5ms
  * `scc::TreeIndex`: 128.7ms
  * `crossbeam_skiplist::SkipSet`: 161.3ms
* 10% writes/90% reads:
  * `indexset::concurrent::set::BTreeSet`: 175.9ms
  * `scc::TreeIndex`: 183.9ms
  * `crossbeam_skiplist::SkipSet`: 217.4ms
* 30% writes/70% reads:
  * `indexset::concurrent::set::BTreeSet`: 190.9ms
  * `scc::TreeIndex`: 313.2ms
  * `crossbeam_skiplist::SkipSet`: 261.8ms
* 50% writes/50% reads:
  * `indexset::concurrent::set::BTreeSet`: 220.75ms
  * `scc::TreeIndex`: 561.70ms
  * `crossbeam_skiplist::SkipSet`: 334.40ms

## Limitations

* `BTreeMap` is less polished than `BTreeSet`. This crate has been optimised for a leaner `BTreeSet`.
* `Concurrent` `BtreeSet`, `BTreeMap` and `BTreeMultiMap` do not support `serde` serialization and deserialization nor are they order-statistic trees.

## Naming

This library is called `indexset` because the base data structure is `BTreeSet`. `BTreeMap` is a `BTreeSet` with
a `Pair<K, V>` item type, and `BTreeMultiMap` is one with a `MultiPair<K, V>` item.

## Changelog

See [CHANGELOG.md](https://github.com/brurucy/indexset/blob/master/CHANGELOG.md).
