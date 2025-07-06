use std::collections::BTreeMap;
use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use flat_rbtree::RedBlackTree;

const N: usize = 10_000;

fn bench_insert_flat_rbtree(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insert - flat_rbtree");
    group.throughput(Throughput::Elements(N as u64));
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Insert 10_000 - flat_rbtree", |b| {
        b.iter(|| {
            let mut tree = RedBlackTree::<usize, usize, N>::new();
            for i in 0..N {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
    group.finish();
}

fn bench_insert_btreemap(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insert - BTreeMap");
    group.throughput(Throughput::Elements(N as u64));
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Insert 10_000 - BTreeMap", |b| {
        b.iter(|| {
            let mut map = BTreeMap::new();
            for i in 0..N {
                map.insert(black_box(i), black_box(i));
            }
        });
    });
    group.finish();
}

fn bench_search_flat_rbtree(c: &mut Criterion) {
    let mut tree = RedBlackTree::<usize, usize, N>::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Search - flat_rbtree");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Search 10_000 - flat_rbtree", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(tree.search(&i));
            }
        });
    });
    group.finish();
}

fn bench_search_btreemap(c: &mut Criterion) {
    let mut map = BTreeMap::new();
    for i in 0..N {
        map.insert(i, i);
    }

    let mut group = c.benchmark_group("Search - BTreeMap");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Search 10_000 - BTreeMap", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(map.get(&i));
            }
        });
    });
    group.finish();
}

fn bench_remove_flat_rbtree(c: &mut Criterion) {
    let mut tree = RedBlackTree::<usize, usize, N>::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    let mut group = c.benchmark_group("Remove - flat_rbtree");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Remove 10_000 - flat_rbtree", |b| {
        b.iter(|| {
            for i in 0..N {
                tree.remove(i);
            }
        });
    });
    group.finish();
}

fn bench_remove_btreemap(c: &mut Criterion) {
    let mut map = BTreeMap::new();
    for i in 0..N {
        map.insert(i, i);
    }

    let mut group = c.benchmark_group("Remove - BTreeMap");
    group.sample_size(20).measurement_time(std::time::Duration::from_secs(10));
    group.bench_function("Remove 10_000 - BTreeMap", |b| {
        b.iter(|| {
            for i in 0..N {
                map.remove(&i);
            }
        });
    });
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets =
        bench_insert_flat_rbtree,
        bench_insert_btreemap,
        bench_remove_flat_rbtree,
        bench_remove_btreemap,
        bench_search_flat_rbtree,
        bench_search_btreemap,
);
criterion_main!(benches);

