use criterion::{criterion_group, criterion_main, Criterion};
use indexset::concurrent2::set::BTreeSet;
use rand::seq::SliceRandom;
use rand::thread_rng;
use scc::TreeIndex;
use std::hint::black_box;

fn criterion_benchmark(c: &mut Criterion) {
    let mut input: Vec<usize> = (0..100000).collect();
    input.shuffle(&mut thread_rng());

    c.bench_function("stdlib insert 100k", |b| {
        b.iter(|| {
            let mut btreeset = std::collections::BTreeSet::new();

            input.iter().for_each(|item| {
                black_box(btreeset.insert(item));
            })
        })
    });
    c.bench_function("indexset insert 100k", |b| {
        b.iter(|| {
            let indexset = BTreeSet::new();

            input.iter().for_each(|item| {
                black_box(indexset.insert(item));
            })
        })
    });
    c.bench_function("treeindex insert 100k", |b| {
        b.iter(|| {
            let treeindex = TreeIndex::new();

            input.iter().for_each(|item| {
                black_box(treeindex.insert(*item, ()).unwrap());
            })
        })
    });

    // let stdlib = std::collections::BTreeSet::from_iter(input.iter());
    // let indexset = BTreeSet::from_iter(input.iter());
    // let treeindex = TreeIndex::new();
    // for i in &input {
    //     treeindex.insert(*i, ());
    // }

    // c.bench_function("stdlib contains 100k", |b| {
    //     b.iter(|| {
    //         input.iter().for_each(|item| {
    //             stdlib.contains(black_box(item));
    //         })
    //     })
    // });
    // c.bench_function("indexset contains 100k", |b| {
    //     b.iter(|| {
    //         input.iter().for_each(|item| {
    //             indexset.contains(black_box(item));
    //         })
    //     })
    // });

    // c.bench_function("treeindex contains 100k", |b| {
    //     b.iter(|| {
    //         input.iter().for_each(|item| {
    //             treeindex.contains(black_box(item));
    //         })
    //     })
    // });

    // c.bench_function("stdlib get i-th 100k", |b| {
    //     b.iter(|| {
    //         input.iter().for_each(|item| {
    //             stdlib.iter().nth(black_box(*item));
    //         })
    //     })
    // });
    /*c.bench_function("indexset get i-th 100k", |b| {
        b.iter(|| {
            input.iter().for_each(|item| {
                black_box(indexset.get_index(black_box(*item)));
            })
        })
    });*/

    /* c.bench_function("stdlib collect 100k into vec", |b| {
        b.iter(|| std::hint::black_box(stdlib.iter().collect::<Vec<&&usize>>()))
    });

    c.bench_function("indexset collect 100k into vec", |b| {
        b.iter(|| std::hint::black_box(indexset.iter().collect::<Vec<&&usize>>()))
    });*/
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
