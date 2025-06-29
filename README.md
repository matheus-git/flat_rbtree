# flat_rbtree

![rust](https://img.shields.io/badge/Rust-000000?style=for-the-badge&logo=rust&logoColor=white)

A fast, index-based Red-Black Tree with no heap allocations — ideal for systems where performance and memory layout matter.

## Features

- **Flat storage**: all nodes are stored in a `Vec`, avoiding pointer indirection.
- **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
- **No-std friendly**: suitable for embedded environments.

## Usage

```rust
let mut tree = RedBlackTree::new();
tree.insert(10, "A");
tree.update(10, "B");
tree.search(10); // Some(&"B")
tree.remove(10);

## 📝 License

This project is open-source under the MIT License.
