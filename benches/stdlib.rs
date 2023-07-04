use criterion::{black_box, criterion_group, criterion_main, Criterion};
use indexset::BTreeSet;
use rand::seq::SliceRandom;
use rand::thread_rng;

fn criterion_benchmark(c: &mut Criterion) {
    let mut input: Vec<usize> = (0..100000).collect();
    input.shuffle(&mut thread_rng());

    c.bench_function("stdlib insert 100k", |b| {
        b.iter(|| std::collections::BTreeSet::from_iter(input.iter()))
    });
    c.bench_function("indexset insert 100k", |b| {
        b.iter(|| BTreeSet::from_iter(input.iter()))
    });

    let stdlib = std::collections::BTreeSet::from_iter(input.iter());
    let indexset = BTreeSet::from_iter(input.iter());

    c.bench_function("stdlib contains 100k", |b| {
        b.iter(|| {
            input.iter().for_each(|item| {
                stdlib.contains(black_box(item));
            })
        })
    });
    c.bench_function("indexset contains 100k", |b| {
        b.iter(|| {
            input.iter().for_each(|item| {
                indexset.contains(black_box(item));
            })
        })
    });

    // c.bench_function("stdlib get i-th 100k", |b| {
    //     b.iter(|| {
    //         input.iter().for_each(|item| {
    //             stdlib.iter().nth(black_box(*item));
    //         })
    //     })
    // });
    c.bench_function("indexset get i-th 100k", |b| {
        b.iter(|| {
            input.iter().for_each(|item| {
                indexset.get(black_box(item));
            })
        })
    });

    c.bench_function("stdlib collect 100k into vec", |b| {
        b.iter(|| std::hint::black_box(stdlib.iter().collect::<Vec<&&usize>>()))
    });

    c.bench_function("indexset collect 100k into vec", |b| {
        b.iter(|| std::hint::black_box(indexset.iter().collect::<Vec<&&usize>>()))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
