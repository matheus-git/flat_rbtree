use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rbtree::RBTree;
use crate::RedBlackTree;

fn bench_insert_custom(c: &mut Criterion) {
    c.bench_function("Insert 10_000 - Custom RBTree", |b| {
        b.iter(|| {
            let mut tree = RedBlackTree::new();
            for i in 0..10_000 {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
}

fn bench_insert_lib(c: &mut Criterion) {
    c.bench_function("Insert 10_000 - rbtree crate", |b| {
        b.iter(|| {
            let mut tree = RBTree::new();
            for i in 0..10_000 {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
}

fn bench_search_custom(c: &mut Criterion) {
    let mut tree = RedBlackTree::new();
    for i in 0..10_000 {
        tree.insert(i, i);
    }
    c.bench_function("Search 10_000 - Custom RBTree", |b| {
        b.iter(|| {
            for i in 0..10_000 {
                black_box(tree.get(&i));
            }
        });
    });
}

fn bench_search_lib(c: &mut Criterion) {
    let mut tree = RBTree::new();
    for i in 0..10_000 {
        tree.insert(i, i);
    }
    c.bench_function("Search 10_000 - rbtree crate", |b| {
        b.iter(|| {
            for i in 0..10_000 {
                black_box(tree.get(&i));
            }
        });
    });
}

criterion_group!(
    benches,
    bench_insert_custom,
    bench_insert_lib,
    bench_search_custom,
    bench_search_lib
);
criterion_main!(benches);
