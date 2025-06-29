# flat_rbtree

![rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)

A fast, index-based Red-Black Tree with no heap allocations — ideal for systems where performance and memory layout matter.

## Features

- **Flat storage**: all nodes are stored in a `Vec`, avoiding pointer indirection.
- **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
- **No-std friendly**: suitable for embedded environments.

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
| **Insert** | 1.93 ms (avg)   | 3.02 ms (avg)  | 
| **Remove** | 2.49 ns         | 0.41 ns        | 
| **Search** | 1.08 ms         | 0.88 ms        | 

> Results may vary depending on hardware and runtime conditions.

## 📝 License

This project is open-source under the MIT License.
