# flat_rbtree

![rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)

A fast, index-based Red-Black Tree with no heap allocations — ideal for systems where performance and memory layout matter.

## Features

- **Flat storage**: all nodes are stored in a `Vec`, avoiding pointer indirection.
- **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
- **Predictable layout**: great for cache locality.
- **No-std friendly** *(optional)*: suitable for embedded environments.
- **Safe Rust**: zero `unsafe` blocks.

## Design Rationale

- Nodes are indexed (usize) instead of heap-allocated.
- Sentinel node used for null-equivalent leaf representation.
- Explicit free-list for reusing memory.
- Inspired by flat ECS-like data layouts and arena-based allocators.

## Usage

```rust
let mut tree = RedBlackTree::new();
tree.insert(10, "A");
tree.search(10); // Some(&"A")
tree.remove(10);
```
## Optional no_std Support

```toml
[dependencies.flat_rbtree]
version = "0.1"
default-features = false
features = ["alloc"]
```

## 📝 License

This project is open-source under the MIT License.
