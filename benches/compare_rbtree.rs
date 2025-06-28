use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion};
use rbtree::RBTree;
use red_black_tree::RedBlackTree;

const N: usize = 100_000;

fn bench_insert_custom(c: &mut Criterion) {
    c.bench_function("Insert 100_000 - Custom RBTree", |b| {
        b.iter(|| {
            let mut tree = RedBlackTree::new();
            for i in 0..N {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
}

fn bench_insert_lib(c: &mut Criterion) {
    c.bench_function("Insert 100_000 - rbtree crate", |b| {
        b.iter(|| {
            let mut tree = RBTree::new();
            for i in 0..N {
                tree.insert(black_box(i), black_box(i));
            }
        });
    });
}

fn bench_remove_custom(c: &mut Criterion) {
    let mut tree = RedBlackTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    c.bench_function("Remove 100_000 - Custom RBTree", |b| {
        b.iter(|| {
            let mut tree_clone = tree.clone();
            for i in 0..N {
                tree_clone.remove(i);
            }
        });
    });
}

fn bench_remove_lib(c: &mut Criterion) {
    let mut tree = RBTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    c.bench_function("Remove 100_000 - rbtree crate", |b| {
        b.iter(|| {
            let mut tree_clone = tree.clone();
            for i in 0..N {
                tree_clone.remove(&i);
            }
        });
    });
}

fn bench_search_custom(c: &mut Criterion) {
    let mut tree = RedBlackTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    c.bench_function("Search 100_000 - Custom RBTree", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(tree.search(i));
            }
        });
    });
}

fn bench_search_lib(c: &mut Criterion) {
    let mut tree = RBTree::new();
    for i in 0..N {
        tree.insert(i, i);
    }

    c.bench_function("Search 100_000 - rbtree crate", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(tree.get(&i));
            }
        });
    });
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

