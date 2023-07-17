# indexset

[![crates.io](https://img.shields.io/crates/v/indexset.svg)](https://crates.io/crates/indexset)
[![docs](https://docs.rs/indexset/badge.svg)](https://docs.rs/indexset)

A pure-Rust two-level dynamic order-statistic b-tree.

This crate implements a compact set data structure that preserves its elements' sorted order and 
allows lookups of entries by value or sorted order position.

Also, it is(mostly) a drop-in replacement for the stdlib BTree.

# Background

This was heavily inspired by [`indexmap`](https://crates.io/crates/indexmap), and 
python's [`sortedcontainers`](https://github.com/grantjenks/python-sortedcontainers).

It differs from both in that:
* `indexmap` is a hashmap that provides numerical lookups, but does not maintain order in case of removals, while
`indexset` is a b-tree that always maintains order, irrespective of which mutating operation is run.
* `sortecontainers` is similar in spirit, but utilizes a different routine for balancing the tree, and relies 
on a heap for numerical lookups.

`indexset` provides the following features:
- As fast to iterate as a vec.
- Zero indirection.
- Lookups by position and range.
- Minimal amount of allocations.
- `select`(lookups by position) and `rank` operations in near constant time.

## Performance

`BTreeSet` and `BTreeMap` derive a couple of performance facts directly from how it is constructed,  which is roughly:

> A two-level B-Tree with a fenwick tree as a low-cost index for numerical lookups

- Iteration is very fast since it inherits a vec's iter struct.
- Insertions and removals are constant time in the best-case scenario, and logarithmic on the node size in the worst 
case
- Lookups are very fast, and rely only on two binary searches over very little data.

## Benchmarks

run `cargo bench` and see it for yourself.

On a lowest-specced M1 macbook pro I got the following numbers:

### Inserting 100k random usize

* `stdlib::collections::BTreeSet.insert(i)`: 8.25ms
* `indexset::BTreeSet.insert(i)`: 17.3ms

### Checking that each 100k random usize integers exist

* `stdlib::collections::BTreeSet.contains(i)`: 7.5ms
* `indexset::BTreeSet.contains(i)`: 6.8ms

### Getting all 100k i-th elements

* `stdlib::collections::BTreeSet.iter.nth(i)`: **13.28s** yes, seconds!
* `indexset::BTreeSet.get_index(i)`: **3.93ms**

### Iterating over all 100k elements and then collecting it into a vec

* `Vec::from_iter(stdlib::collections::BTreeSet.iter())`: **227.28us**
* `Vec::from_iter(indexset::BTreeSet.iter())`: **123.21.us**

Yes.

Getting the i-th element is **3400x** faster than stdlib's btree, `contains` is 10% faster, and iterating
is twice as fast, at the cost of insertions being half as fast.

If your use case of `std::collections::BTreeSet` and `BTreeMap` is more read-heavy, or if you really need to index by
sorted-order position, it might be worth checking out this `indexset` instead.

# Limitations

* `BTreeMap` is less polished than `BTreeSet`. This crate has been optimised for a leaner `BTreeSet`.
* This is **beta** quality software, so use it at your own risk. I'm not 100% certain about every single iterator
implementation(everything has tests though).
* There's quite a couple utility traits that have not been implemented yet.

# Naming

This library is called `indexset`, because the base data structure is `BTreeSet`. `BTreeMap` is a `BTreeSet` with 
a `Pair<K, V>` item type.

# Changelog

See [CHANGELOG.md](https://github.com/brurucy/indexset/blob/master/CHANGELOG.md).