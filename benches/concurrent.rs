use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use indexset::concurrent2::set::BTreeSet;
use rand::{thread_rng, Rng};
use scc::TreeIndex;
use std::sync::{Arc, RwLock};
use std::thread;

#[derive(Clone)]
enum Op {
    Read(usize),
    Write(usize),
}

const NUM_READERS: usize = 32;
const NUM_WRITERS: usize = 1;
const NUM_THREADS: usize = NUM_READERS + NUM_WRITERS;
const OPERATIONS_PER_THREAD: usize = 10_000;
const TOTAL_OPERATIONS: usize = NUM_THREADS * OPERATIONS_PER_THREAD;

fn generate_operations(write_ratio: f64) -> Vec<Vec<Op>> {
    let mut rng = thread_rng();
    let mut all_operations: Vec<Vec<Op>> =
        vec![Vec::with_capacity(OPERATIONS_PER_THREAD); NUM_THREADS];

    for i in 0..TOTAL_OPERATIONS {
        let thread_index = i % NUM_THREADS;
        let value = rng.gen_range(0..TOTAL_OPERATIONS);
        let operation = if thread_index == NUM_READERS || rng.gen::<f64>() < write_ratio {
            Op::Write(value)
        } else {
            Op::Read(value)
        };
        all_operations[thread_index].push(operation);
    }

    all_operations
}

fn concurrent_operations<T: Send + Sync + 'static>(
    set: Arc<T>,
    operations: Vec<Op>,
    read_op: impl Fn(&T, usize) + Send + Sync + 'static,
    write_op: impl Fn(&T, usize) + Send + Sync + 'static,
) {
    for op in operations {
        match op {
            Op::Read(value) => read_op(&set, value),
            Op::Write(value) => write_op(&set, value),
        }
    }
}

fn bench_btreeset_with_ratio(c: &mut Criterion, write_ratio: f64) {
    let operations = Arc::new(generate_operations(write_ratio));

    let mut group = c.benchmark_group(format!("Write Ratio: {:.2}", write_ratio));

    group.bench_function(BenchmarkId::new("scc::TreeIndex", write_ratio), |b| {
        b.iter(|| {
            let set = Arc::new(TreeIndex::new());
            let mut handles = vec![];

            for thread_ops in operations.iter() {
                let set = Arc::clone(&set);
                let thread_ops = thread_ops.clone();
                let handle = thread::spawn(move || {
                    concurrent_operations(
                        set,
                        thread_ops,
                        |set, item| {
                            black_box(set.contains(&item));
                        },
                        |set, item| {
                            black_box({
                                let _ = set.insert(item, ());
                            });
                        },
                    );
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    group.bench_function(
        BenchmarkId::new("indexset::concurrent::set::BTreeSet", write_ratio),
        |b| {
            b.iter(|| {
                let set = Arc::new(BTreeSet::new());
                let mut handles = vec![];

                for thread_ops in operations.iter() {
                    let set = Arc::clone(&set);
                    let thread_ops = thread_ops.clone();
                    let handle = thread::spawn(move || {
                        concurrent_operations(
                            set,
                            thread_ops,
                            |set, item| {
                                set.contains(&item);
                            },
                            |set, item| {
                                set.insert(item);
                            },
                        );
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    handle.join().unwrap();
                }
            });
        },
    );

    group.bench_function(
        BenchmarkId::new("RwLock<std::collections::BTreeSet>", write_ratio),
        |b| {
            b.iter(|| {
                let set = Arc::new(RwLock::new(std::collections::BTreeSet::new()));
                let mut handles = vec![];

                for thread_ops in operations.iter() {
                    let set = Arc::clone(&set);
                    let thread_ops = thread_ops.clone();
                    let handle = thread::spawn(move || {
                        concurrent_operations(
                            set,
                            thread_ops,
                            |set, item| {
                                set.read().unwrap().contains(&item);
                            },
                            |set, item| {
                                set.write().unwrap().insert(item);
                            },
                        );
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    handle.join().unwrap();
                }
            });
        },
    );

    group.finish();
}

fn bench_concurrent_btreeset(c: &mut Criterion) {
    let ratios = vec![0.01, 0.1, 0.3];
    for ratio in ratios {
        bench_btreeset_with_ratio(c, ratio);
    }
}

criterion_group!(benches, bench_concurrent_btreeset);
criterion_main!(benches);
