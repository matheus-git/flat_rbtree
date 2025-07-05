use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use rbtree::RBTree;
use flat_rbtree::RedBlackTree;

const N: usize = 10_000;

fn bench_insert_custom(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insert - Custom RBTree");
    group.throughput(Throughput::Elements(N as u64));
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Insert 10_000 - Custom RBTree", |b| {
        b.iter(|| {
            let mut tree = RedBlackTree::<usize, usize, N>::new();
            for i in 0..N {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
    group.finish();
}

fn bench_insert_lib(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insert - rbtree crate");
    group.throughput(Throughput::Elements(N as u64));
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Insert 10_000 - rbtree crate", |b| {
        b.iter(|| {
            let mut tree = RBTree::new();
            for i in 0..N {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
    group.finish();
}

fn bench_remove_custom(c: &mut Criterion) {
    let mut tree = RedBlackTree::<usize, usize, N>::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Remove - Custom RBTree");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Remove 10_000 - Custom RBTree", |b| {
        b.iter(|| {
            for i in 0..N {
                tree.remove(i);
            }
        });
    });
    group.finish();
}

fn bench_remove_lib(c: &mut Criterion) {
    let mut tree = RBTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Remove - rbtree crate");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Remove 10_000 - rbtree crate", |b| {
        b.iter(|| {
            for i in 0..N {
                tree.remove(&i);
            }
        });
    });
    group.finish();
}

fn bench_search_custom(c: &mut Criterion) {
    let mut tree = RedBlackTree::<usize, usize, N>::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Search - Custom RBTree");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Search 10_000 - Custom RBTree", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(tree.search(&i));
            }
        });
    });
    group.finish();
}

fn bench_search_lib(c: &mut Criterion) {
    let mut tree = RBTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Search - rbtree crate");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Search 10_000 - rbtree crate", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(tree.get(&i));
            }
        });
    });
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets =
        bench_insert_custom,
        bench_insert_lib,
        bench_remove_custom,
        bench_remove_lib,
        bench_search_custom,
        bench_search_lib,
);
criterion_main!(benches);

