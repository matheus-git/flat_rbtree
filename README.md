# flat_rbtree

![rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)

A fast, index-based Red-Black Tree with no heap allocations — ideal for systems where performance and memory layout matter.

## Features

- **Flat storage**: all nodes are stored in a `array`, avoiding pointer indirection.
- **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
- **No-std**: suitable for embedded environments.
- **Preallocated with MaybeUninit**: minimizes runtime overhead and ensures memory safety.

## Usage

```rust
let mut tree = RedBlackTree::<&str, i32, 1>::new();
tree.insert("A", 1);
tree.update("A", 2);
tree.search("A"); // Some(&2)
tree.remove("A");
```

## Benchmark: flat_rbtree vs [rbtree](https://docs.rs/rbtree/latest/rbtree/) (10,000 operations)

| Operation | flat_rbtree | [rbtree](https://docs.rs/rbtree/latest/rbtree/) |
|-----------|----------------|---------------|
| **Insert** | 1.14 ms   | 1.34 ms  | 
| **Remove** | 2.12 ns        | 354 ps       | 
| **Search** | 655 µs         | 514 µs       | 

> It’s worth noting that `rbtree` is a pointer-based implementation, which tends to be more performant than an index-based implementation.

## 📝 License

This project is open-source under the MIT License.
