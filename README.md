# flat_rbtree

![rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)

A fast, index-based Red-Black Tree with no heap allocations — ideal for systems where performance and memory layout matter.

See [Documentation](https://docs.rs/flat_rbtree/0.2.3)

## Features

- **Flat storage**: all nodes are stored in a `array`, avoiding pointer indirection.
- **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
- **No-std**: works in embedded or bare-metal environments without relying on the Rust standard library..
- **Preallocated with MaybeUninit**: memory for all nodes is allocated upfront, minimizing runtime overhead and ensuring safe initialization.
- **Fixed capacity**: tree size is bounded at compile-time, making resource usage predictable.
- **`expanded` feature** *(optional)*: enables tracking of subtree sizes for each node,
  allowing support for `rank`, `select`, and `range_count` queries.

## Simple usage

```rust
use flat_rbtree::RedBlackTree;

let mut tree = RedBlackTree::<i32, &str, 10>::new();

tree.insert(10, "A");
tree.insert(20, "B");
tree.insert(5, "C");

tree.update(10, "Updated A");

if let Some(value) = tree.search(&10) {
    println!("Key 10 has value: {}", value);
}

for (key, value) in tree.iter() {
    println!("Key: {}, Value: {}", key, value);
}

tree.remove(20);

if !tree.contains_key(&20) {
    println!("Key 20 successfully removed");
}
```

## Benchmark: `flat_rbtree` vs [rbtree](https://docs.rs/rbtree/latest/rbtree/) (10,000 operations)

| Operation | `flat_rbtree` | `rbtree` |
|-----------|----------------|---------------|
| **Insert** | 1.14 ms   | 1.34 ms  | 
| **Remove** | 2.12 ns        | 0.35 ns       | 
| **Search** | 655 µs         | 514 µs       | 

## Benchmark: `flat_rbtree` vs [`BTreeMap`](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html) (10,000 operations)

| Operation | `flat_rbtree`          | `BTreeMap`             |
|-----------|------------------------|-------------------------|
| **Insert** | 1.14 ms  | 0.89 ms  |
| **Remove** | 2.12 ns              |  18,90 ns                 |
| **Search** | 702 µs                 | 524 µs                  |


## 📝 License

This project is open-source under the MIT License.
