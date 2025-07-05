#![allow(warnings)]
#![no_std]

//! A fast, index-based Red-Black Tree with no heap allocations.
//!
//! ## Features
//! - **Flat storage**: all nodes are stored in an `array`, avoiding pointer indirection.
//! - **No allocations per node**: avoids `Box`, `Rc`, or `Arc`.
//! - **No-std**: works in embedded or bare-metal environments without relying on the Rust standard library.
//! - **Preallocated with `MaybeUninit`**: memory for all nodes is allocated upfront, minimizing runtime overhead and ensuring safe initialization.
//! - **Fixed capacity**: tree size is bounded at compile-time, making resource usage predictable.
//! - **`expanded` feature** *(optional)*: enables tracking of subtree sizes for each node,
//!   allowing support for `rank`, `select`, and `range_count` queries.
//!
//! ## Simple example
//! ```
//! use flat_rbtree::RedBlackTree;
//!
//! let mut tree = RedBlackTree::<i32, &str, 10>::new();
//!
//! tree.insert(10, "A");
//! tree.insert(20, "B");
//! tree.insert(5, "C");
//!
//! tree.update(10, "Updated A");
//!
//! if let Some(value) = tree.search(&10) {
//!     println!("Key 10 has value: {}", value);
//! }
//!
//! for (key, value) in tree.iter() {
//!     println!("Key: {}, Value: {}", key, value);
//! }
//!
//! assert_eq!(tree.remove(20), true);
//!
//! if !tree.contains_key(&20) {
//!     println!("Key 20 successfully removed");
//! }
//! ```
//!
use core::mem::MaybeUninit;
use core::cmp::Ordering;

const SENTINEL: usize = usize::MAX;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum Color {
    Red,
    Black,
}

#[derive(Debug)]
struct Node<K, V> {
    key: K,
    value: V,
    color: Color,
    parent: usize,
    left: usize,
    right: usize,
    #[cfg(feature = "expanded")]
    size: usize
}

/// An iterator over the entries of a `RedBlackTree`.
pub struct RedBlackTreeIter<'a, K: Ord + 'a, V: 'a, const N: usize> {
    tree: &'a RedBlackTree<K, V, N>,
    current: usize,
    end: usize
}

impl<'a, K: Ord + 'a, V: 'a, const N: usize> Iterator for RedBlackTreeIter<'a, K, V, N> {
    type Item = (&'a K, &'a V);

    /// Advances the iterator and returns the next key-value pair in ascending order.
    fn next(&mut self) -> Option<Self::Item> {
        if self.current == SENTINEL || self.current == self.end {
            return None;
        }

        let current_node = self.tree.get_node_by_index(self.current);
        let item = (&current_node.key, &current_node.value);

        self.current = self.tree.successor(self.current);

        Some(item)
    }
}

impl<'a, K: Ord + 'a, V: 'a, const N: usize> DoubleEndedIterator for RedBlackTreeIter<'a, K, V, N> {
    /// Advances the iterator from the back and returns the previous key-value pair in descending order.
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.current == SENTINEL || self.current == self.end {
            return None;
        }

        let current_node = self.tree.get_node_by_index(self.current);
        let item = (&current_node.key, &current_node.value);

        self.current = self.tree.predecessor(self.current);

        Some(item)
    }
}


/// Index-based Red-Black Tree implementation
#[derive(Debug)]
pub struct RedBlackTree<K: Ord, V, const N: usize> {
    nodes: [MaybeUninit<Node<K, V>>; N],
    free_indexes: [usize;N],
    free_len: usize,
    root: usize
}

impl<K: Ord, V, const N: usize> RedBlackTree<K,V,N> {
    /// Creates a new empty red-black tree with capacity for up to `N` elements.
    ///
    /// Nodes are preallocated using `MaybeUninit`, and no heap allocations are performed.
    pub fn new() -> Self {
        let mut free_indexes = [0; N];
        for (i, v) in (0..N).rev().enumerate() {
            free_indexes[i] = v;
        }

        Self {
            nodes: unsafe { MaybeUninit::uninit().assume_init() },
            free_indexes,
            free_len: N,
            root: SENTINEL,
        }
    }

    /// Searches for a value associated with the given key.
    ///
    /// Returns a reference to the value if the key is found, or `None` otherwise.
    #[inline(always)]
    pub fn search(&self, key: &K) -> Option<&V> {
        let x = self.get_index_by_key(&key);
        if x == SENTINEL{
            return None;
        }
        let z = self.get_node_by_index(x);
        Some(&z.value)
    }
    
    /// Inserts a key-value pair into the tree.
    ///
    /// If the key already exists, its value is replaced.
    #[inline(always)]
    pub fn insert(&mut self, key: K, value: V) -> Option<&V> {
        let mut x = self.root;
        let mut y = SENTINEL;

        while x != SENTINEL {
            y = x;

            let y_node = self.get_node_by_index(y);

            match key.cmp(&y_node.key) {
                Ordering::Less => x = y_node.left,
                Ordering::Greater => x = y_node.right,
                Ordering::Equal => {
                    self.get_mut_node_by_index(x).value = value;
                    return None;
                },
            }
        }

        let new_node = Node {
            key,
            value,
            color: Color::Red,
            parent: SENTINEL,
            left: SENTINEL,
            right: SENTINEL,
            #[cfg(feature = "expanded")]
            size: 1
        };

        let new_node_index = if self.free_len > 0 {
            self.free_len -= 1;
            let index = self.free_indexes[self.free_len];
            self.nodes[index] = MaybeUninit::new(new_node);
            index
        } else {
            panic!("RedBlackTree is full. Consider increasing N.");
        };

        let new_node = self.get_node_by_index(new_node_index);
        let new_key = &new_node.key;

        self.get_mut_node_by_index(new_node_index).parent = y;
        if y == SENTINEL {
            self.root = new_node_index;
        } else {
            if self.get_node_by_index(new_node_index).key < self.get_node_by_index(y).key {
                self.get_mut_node_by_index(y).left = new_node_index;
            } else {
                self.get_mut_node_by_index(y).right = new_node_index;
            }
        }

        self.insert_fixup(new_node_index);
        #[cfg(feature = "expanded")]
        self.fix_sizes_upward(new_node_index);

        Some(&self.get_node_by_index(new_node_index).value)
    }

    #[inline(always)]
    fn get_index_by_key(&self, key: &K) -> usize {
        let mut z = self.root;

        while z != SENTINEL {
            let node = self.get_node_by_index(z);
            match key.cmp(&node.key) {
                Ordering::Less => z = node.left,
                Ordering::Greater => z = node.right,
                Ordering::Equal => return z,
            }
        }

        SENTINEL
    }

    /// Updates the value for an existing key.
    ///
    /// If the key is not found, it is inserted with the provided value.
    #[inline(always)]
    pub fn update(&mut self, key: K, value: V) -> Option<&V>{
        let z = self.get_index_by_key(&key); 

        if z == SENTINEL {
            return self.insert(key, value);
        }

        self.get_mut_node_by_index(z).value = value;
        Some(&self.get_node_by_index(z).value)
    }

    #[inline(always)]
    fn insert_fixup(&mut self, mut z: usize) {
        while z != SENTINEL
            && self.get_node_by_index(z).parent != SENTINEL
            && self.is_red(z)
            && self.is_red(self.get_node_by_index(z).parent)
        {
            let mut z_parent = self.get_node_by_index(z).parent;
            let mut z_grand = self.get_node_by_index(z_parent).parent;
            let z_parent_node = self.get_node_by_index(z_parent);
            let z_grand_node = self.get_node_by_index(z_grand);

            if z_parent == z_grand_node.left {
                let uncle = z_grand_node.right;
                if uncle != SENTINEL && self.is_red(uncle) {
                    self.get_mut_node_by_index(z_parent).color = Color::Black;
                    self.get_mut_node_by_index(uncle).color = Color::Black;
                    self.get_mut_node_by_index(z_grand).color = Color::Red;
                    z = z_grand;
                } else {
                    if z == z_parent_node.right {
                        z = z_parent;
                        self.rotate_left(z);
                    }
                    z_parent = self.get_node_by_index(z).parent;
                    z_grand = self.get_node_by_index(z_parent).parent;
                    if z_grand != SENTINEL {
                        self.get_mut_node_by_index(z_parent).color = Color::Black;
                        self.get_mut_node_by_index(z_grand).color = Color::Red;
                        self.rotate_right(z_grand);
                    }
                }
            } else {
                let uncle = z_grand_node.left;
                if uncle != SENTINEL && self.is_red(uncle) {
                    self.get_mut_node_by_index(z_parent).color = Color::Black;
                    self.get_mut_node_by_index(uncle).color = Color::Black;
                    self.get_mut_node_by_index(z_grand).color = Color::Red;
                    z = z_grand;
                } else {
                    if z == z_parent_node.left {
                        z = z_parent;
                        self.rotate_right(z);
                    }
                    z_parent = self.get_node_by_index(z).parent;
                    z_grand = self.get_node_by_index(z_parent).parent;
                    if z_grand != SENTINEL {
                        self.get_mut_node_by_index(z_parent).color = Color::Black;
                        self.get_mut_node_by_index(z_grand).color = Color::Red;
                        self.rotate_left(z_grand);
                    }
                }
            }
        }
        self.get_mut_node_by_index(self.root).color = Color::Black;
    }

    #[cfg(feature = "expanded")]
    #[inline(always)]
    fn get_node_size(&self, x: usize) -> usize {
        if SENTINEL == x {
            return 0;
        }
        self.get_node_by_index(x).size
    }

    #[cfg(feature = "expanded")]
    #[inline(always)]
    fn recompute_size(&mut self, x: usize) {
        if x == SENTINEL {
            return;
        }
        let (left, right) = {
            let node = self.get_node_by_index(x);
            (node.left, node.right)
        };
        let left_size = self.get_node_size(left);
        let right_size = self.get_node_size(right);
        self.get_mut_node_by_index(x).size = 1 + left_size + right_size;
    }

    #[inline(always)]
    fn rotate_left(&mut self, x: usize) {
        let y = self.get_node_by_index(x).right;
        if y == SENTINEL {
            return;
        }

        let y_left_child = self.get_node_by_index(y).left;
        {
            let x_node = self.get_mut_node_by_index(x);
            x_node.right = y_left_child;
        }

        if y_left_child != SENTINEL {
            self.get_mut_node_by_index(y_left_child).parent = x;
        }

        let x_parent = self.get_node_by_index(x).parent;
        {
            let y_node = self.get_mut_node_by_index(y);
            y_node.parent = x_parent;
        }

        if x_parent == SENTINEL {
            self.root = y;
        } else {
            let x_parent_node = self.get_mut_node_by_index(x_parent);
            if x == x_parent_node.left {
                x_parent_node.left = y;
            } else {
                x_parent_node.right = y;
            }
        }

        {
            let y_node = self.get_mut_node_by_index(y);
            y_node.left = x;
        }
        self.get_mut_node_by_index(x).parent = y;
        
        #[cfg(feature = "expanded")]
        self.fix_sizes_upward(x);
    }

    #[inline(always)]
    fn rotate_right(&mut self, x: usize) {
        let y = self.get_node_by_index(x).left;
        if y == SENTINEL {
            return;
        }

        let y_right_child = self.get_node_by_index(y).right;
        {
            let x_node = self.get_mut_node_by_index(x);
            x_node.left = y_right_child;
        }

        if y_right_child != SENTINEL {
            self.get_mut_node_by_index(y_right_child).parent = x;
        }

        let x_parent = self.get_node_by_index(x).parent;
        {
            let y_node = self.get_mut_node_by_index(y);
            y_node.parent = x_parent;
        }

        if x_parent == SENTINEL {
            self.root = y;
        } else {
            let x_parent_node = self.get_mut_node_by_index(x_parent);
            if x == x_parent_node.right {
                x_parent_node.right = y;
            } else {
                x_parent_node.left = y;
            }
        }

        {
            let y_node = self.get_mut_node_by_index(y);
            y_node.right = x;
        }
        self.get_mut_node_by_index(x).parent = y;
        
        #[cfg(feature = "expanded")]
        self.fix_sizes_upward(x);
    } 

    #[cfg(feature = "expanded")]
    #[inline(always)]
    fn fix_sizes_upward(&mut self, mut node: usize) {
        while node != SENTINEL {
            let (left, right) = {
                let n = self.get_node_by_index(node);
                (n.left, n.right)
            };
            let size = 1 + self.get_node_size(left) + self.get_node_size(right);
            self.get_mut_node_by_index(node).size = size;

            node = self.get_node_by_index(node).parent;
        }
    }

    /// Returns a reference to the smallest (minimum) key-value pair in the tree, if any.
    pub fn min(&self) -> Option<(&K, &V)> {
        let mut x = self.root;
        if x == SENTINEL {
            return None
        }
        while self.get_node_by_index(x).left != SENTINEL {
            x = self.get_node_by_index(x).left;
        }
        let item = self.get_node_by_index(x);
        Some((&item.key, &item.value))
    }

    /// Returns a reference to the largest (maximum) key-value pair in the tree, if any.
    pub fn max(&self) -> Option<(&K, &V)> {
        let mut x = self.root;
        if x == SENTINEL {
            return None
        }
        while self.get_node_by_index(x).right != SENTINEL {
            x = self.get_node_by_index(x).right;
        }
        let item = self.get_node_by_index(x);
        Some((&item.key, &item.value))
    }

    fn min_usize(&self, mut x: usize) -> usize {
        if x == SENTINEL {
            return x
        }
        while self.get_node_by_index(x).left != SENTINEL {
            x = self.get_node_by_index(x).left;
        }
        x
    }

    fn max_usize(&self, mut x: usize) -> usize {
        if x == SENTINEL {
            return x
        }
        while self.get_node_by_index(x).right != SENTINEL {
            x = self.get_node_by_index(x).right;
        }
        x
    }

    fn successor(&self, mut x: usize) -> usize {
        if x == SENTINEL {
            return x
        }

        if self.get_node_by_index(x).right != SENTINEL {
            return self.min_usize(self.get_node_by_index(x).right)
        }
        
        let mut y = self.get_node_by_index(x).parent;

        while y != SENTINEL && x == self.get_node_by_index(y).right {
            x = y;
            y = self.get_node_by_index(y).parent;
        }
        y
    }

    fn predecessor(&self, mut x: usize) -> usize {
        if x == SENTINEL {
            return x;
        }

        if self.get_node_by_index(x).left != SENTINEL {
            return self.max_usize(self.get_node_by_index(x).left);
        }

        let mut y = self.get_node_by_index(x).parent;

        while y != SENTINEL && x == self.get_node_by_index(y).left {
            x = y;
            y = self.get_node_by_index(y).parent;
        }

        y
    }

    #[inline(always)]
    fn transplant(&mut self, u: usize, v: usize) {
        let u_parent = self.get_node_by_index(u).parent;
        if self.get_node_by_index(u).parent == SENTINEL {
            self.root = v;
        } else if u == self.get_node_by_index(self.get_node_by_index(u).parent).left {
            self.get_mut_node_by_index(u_parent).left = v;
        } else {
            self.get_mut_node_by_index(u_parent).right = v;
        }

        if v != SENTINEL {
            self.get_mut_node_by_index(v).parent = self.get_node_by_index(u).parent;
        }
        #[cfg(feature = "expanded")]
        self.recompute_size(v);
        #[cfg(feature = "expanded")]
        self.fix_sizes_upward(u_parent);
    }

    // Removes a key (and its associated value) from the tree.
    ///
    /// If the key is not found, nothing happens.
    #[inline(always)]
    pub fn remove(&mut self, key: K) -> bool {
        let mut z = self.get_index_by_key(&key);
        if z == SENTINEL {
            return false;
        }

        let mut y = z;
        let x;

        let (z_left, z_right, z_color) = {
            let z_node = self.get_node_by_index(z);
            (z_node.left, z_node.right, z_node.color)
        };

        let mut y_original_color = z_color;;

        if z_left == SENTINEL {
            x = z_right;
            y_original_color = z_color;
            self.transplant(z, z_right);
        } else if z_right == SENTINEL {
            x = z_left;
            y_original_color = z_color;
            self.transplant(z, z_left);
        } else {
            y = self.min_usize(z_right);
            let (y_right, y_color) = {
                let y_node = self.get_node_by_index(y);
                (y_node.right, y_node.color)
            };
            x = y_right;
            y_original_color = y_color;

            if y != z_right {
                self.transplant(y, y_right);
                self.get_mut_node_by_index(y).right = z_right;
                self.get_mut_node_by_index(z_right).parent = y;
            } else if x != SENTINEL {
                self.get_mut_node_by_index(x).parent = y;
            }

            self.transplant(z, y);
            self.get_mut_node_by_index(y).left = z_left;
            self.get_mut_node_by_index(z_left).parent = y;
            self.get_mut_node_by_index(y).color = z_color;
            #[cfg(feature = "expanded")]
            self.recompute_size(y);
        }

        if y_original_color == Color::Black {
            self.remove_fix(x);
        }

        let mut node_to_fix = if x != SENTINEL {
            x
        } else {
            self.get_node_by_index(z).parent
        };

        #[cfg(feature = "expanded")]
        self.fix_sizes_upward(node_to_fix);

        self.free_indexes[self.free_len] = z;
        self.free_len += 1;
        true
    }

    #[inline(always)]
    fn remove_fix(&mut self, mut x: usize) {
        while x != self.root && x != SENTINEL && self.is_black(x) {
            let x_parent = self.get_node_by_index(x).parent;
            let x_parent_node = self.get_node_by_index(x_parent);
            let x_is_left = x == x_parent_node.left;

            let mut cousin = if x_is_left {
                x_parent_node.right
            } else {
                x_parent_node.left
            };

            if cousin == SENTINEL {
                x = x_parent;
                continue;
            }

            if self.is_red(cousin) {
                {
                    let cousin_mut = self.get_mut_node_by_index(cousin);
                    cousin_mut.color = Color::Black;
                }
                self.get_mut_node_by_index(x_parent).color = Color::Red;

                if x_is_left {
                    self.rotate_left(x_parent);
                    cousin = self.get_node_by_index(x_parent).right;
                } else {
                    self.rotate_right(x_parent);
                    cousin = self.get_node_by_index(x_parent).left;
                }

                if cousin == SENTINEL {
                    x = x_parent;
                    continue;
                }
            }

            let c_node = self.get_node_by_index(cousin);
            let (mut c_left, mut c_right) = (c_node.left, c_node.right);

            let left_black = c_left == SENTINEL || self.is_black(c_left);
            let right_black = c_right == SENTINEL || self.is_black(c_right);

            if left_black && right_black {
                self.get_mut_node_by_index(cousin).color = Color::Red;
                x = x_parent;
            } else {
                if x_is_left {
                    if self.is_black(c_right) {
                        if c_left != SENTINEL {
                            self.get_mut_node_by_index(c_left).color = Color::Black;
                        }
                        self.get_mut_node_by_index(cousin).color = Color::Red;
                        self.rotate_right(cousin);
                        cousin = self.get_node_by_index(x_parent).right;
                        c_right = self.get_node_by_index(cousin).right;
                    }

                    let parent_color = self.get_node_by_index(x_parent).color;
                    self.get_mut_node_by_index(cousin).color = parent_color;
                    self.get_mut_node_by_index(x_parent).color = Color::Black;

                    if c_right != SENTINEL {
                        self.get_mut_node_by_index(c_right).color = Color::Black;
                    }
                    self.rotate_left(x_parent);
                } else {
                    if self.is_black(c_left) {
                        if c_right != SENTINEL {
                            self.get_mut_node_by_index(c_right).color = Color::Black;
                        }
                        self.get_mut_node_by_index(cousin).color = Color::Red;
                        self.rotate_left(cousin);
                        cousin = self.get_node_by_index(x_parent).left;
                        c_left = self.get_node_by_index(cousin).left;
                    }

                    let parent_color = self.get_node_by_index(x_parent).color;
                    self.get_mut_node_by_index(cousin).color = parent_color;
                    self.get_mut_node_by_index(x_parent).color = Color::Black;

                    if c_left != SENTINEL {
                        self.get_mut_node_by_index(c_left).color = Color::Black;
                    }
                    self.rotate_right(x_parent);
                }

                x = self.root;
            }
        }

        if x != SENTINEL {
            self.get_mut_node_by_index(x).color = Color::Black;
        }
    }

    #[inline(always)]
    fn is_black(&self, index: usize) -> bool {
        index == SENTINEL || Color::Black == self.get_node_by_index(index).color
    }

    #[inline(always)]
    fn is_red(&self, index: usize) -> bool {
        index != SENTINEL && Color::Red == self.get_node_by_index(index).color
    }

    #[inline(always)]
    fn get_node_by_index(&self, x: usize) -> &Node<K,V> {
        debug_assert_ne!(x, SENTINEL);
        unsafe {
            return self.nodes[x].assume_init_ref()
        }   
    }

    #[inline(always)]
    fn get_mut_node_by_index(&mut self, x: usize) -> &mut Node<K,V> {
        debug_assert_ne!(x, SENTINEL);
        unsafe {
            return self.nodes[x].assume_init_mut()
        }
    }
    
    /// Returns an iterator over the key-value pairs of the tree in ascending key order.
    pub fn iter(&self) -> RedBlackTreeIter<'_, K, V, N> {
        RedBlackTreeIter {
            tree: self,
            current: self.min_usize(self.root),
            end: SENTINEL
        }
    }

    /// Returns an iterator over the entries in the range [`start`, `end`),
    pub fn range_iter(&self, start: &K, end: &K) -> RedBlackTreeIter<'_, K, V, N> {
        if start >= end {
            return RedBlackTreeIter {
                tree: self,
                current: SENTINEL,
                end: SENTINEL,
            };
        }

        let mut current = self.root;
        let mut start_index = SENTINEL;
        let mut end_index = SENTINEL;

        while current != SENTINEL {
            let node = self.get_node_by_index(current);
            if &node.key >= start {
                start_index = current;
                current = node.left;
            } else {
                current = node.right;
            }
        }

        current = self.root;

        while current != SENTINEL {
            let node = self.get_node_by_index(current);
            if &node.key >= end {
                end_index = current;
                current = node.left;
            } else {
                current = node.right;
            }
        }
        RedBlackTreeIter {
            tree: self,
            current: start_index,
            end: end_index,
        }
    }

    /// Checks if the red-black tree invariants are preserved.
    pub fn is_valid(&self) -> bool {
        if self.root == SENTINEL {
            return true;
        }

        if self.is_red(self.root) {
            return false;
        }

        self.validate(self.root).is_some()
    }

    fn validate(&self, idx: usize) -> Option<usize> {
        if idx == SENTINEL {
            return Some(1);
        }

        let node = self.get_node_by_index(idx);

        if node.color == Color::Red {
            if node.left != SENTINEL && self.is_red(node.left) {
                return None;
            }
            if node.right != SENTINEL && self.is_red(node.right) {
                return None;
            }
        }

        let left_black = self.validate(node.left)?;
        let right_black = self.validate(node.right)?;

        if left_black != right_black {
            return None;
        }

        Some(left_black + if node.color == Color::Black { 1 } else { 0 })
    }


    pub fn contains_key(&self, key: &K) -> bool {
        let x = self.get_index_by_key(key);
        if SENTINEL == x {
            return false
        }
        true
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let x = self.get_index_by_key(key);
        if SENTINEL == x {
            return None
        }
        Some(&mut self.get_mut_node_by_index(x).value)
    }

    pub fn len(&self) -> usize {
        N - self.free_len
    }

    pub fn isEmpty(&self) -> bool {
        self.len() == N
    }

    #[cfg(feature = "expanded")]
    /// Returns the number of keys less than the given `key`.
    pub fn rank(&self, key: &K) -> usize {
        let mut rank = 0;
        let mut current = self.root;

        while current != SENTINEL {
            let node = self.get_node_by_index(current);

            if *key < node.key {
                current = node.left;
            } else {
                let left_size = self.get_node_size(node.left);
                rank += left_size;
                if *key > node.key {
                    rank += 1;
                }
                current = node.right;
            }
        }

        rank
    }

    #[cfg(feature = "expanded")]
    /// Returns a reference to the key with the given `k`-th smallest rank (0-based).
    pub fn select(&self, mut k: usize) -> Option<&K> {
        let mut current = self.root;

        while current != SENTINEL {
            let node = self.get_node_by_index(current);
            let left_size = self.get_node_size(node.left);

            match k.cmp(&left_size) {
                Ordering::Less => {
                    current = node.left;
                }
                Ordering::Equal => {
                    return Some(&node.key);
                }
                Ordering::Greater => {
                    k -= left_size + 1;
                    current = node.right;
                }
            }
        }

        None
    }

    #[cfg(feature = "expanded")]
    /// Returns the number of elements in the range [`start`, `end`].
    pub fn range_count(&self, start: &K, end: &K) -> usize {
        if start >= end {
            return 0;
        }

        self.rank(end) - self.rank(start)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_small_tree() -> RedBlackTree<i32, &'static str, 10> {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();
        tree.insert(10, "A");
        tree.insert(20, "B");
        tree.insert(5, "C");
        tree
    }

    #[cfg(feature = "expanded")]
    fn validate_node_sizes<K: Ord + Copy, V, const N: usize>(tree: &RedBlackTree<K, V, N>, node_index: usize) -> usize {
        if node_index == SENTINEL {
            return 0;
        }

        let node = tree.get_node_by_index(node_index);

        let left_size = validate_node_sizes(tree, node.left);
        let right_size = validate_node_sizes(tree, node.right);

        let expected_size = 1 + left_size + right_size;

        assert_eq!(
            node.size, expected_size,
            "Node at index {} has incorrect size: expected {}, got {}",
            node_index, expected_size, node.size
        );

        expected_size
    }

    #[cfg(feature = "expanded")]
    #[test]
    fn test_range_iter_completo() {
        let mut tree = RedBlackTree::<i32, &str, 15>::new();

        tree.insert(10, "A");
        tree.insert(20, "B");
        tree.insert(30, "C");
        tree.insert(40, "D");
        tree.insert(50, "E");
        tree.insert(60, "F");
        tree.insert(70, "G");

        let mut results: [(i32, &str); 15] = [(0, ""); 15];
        let mut count;

        count = 0;
        for (k, v) in tree.range_iter(&15, &55) {
            results[count] = (*k, *v);
            count += 1;
        }
        let expected1 = [(20, "B"), (30, "C"), (40, "D"), (50, "E")];
        assert_eq!(&results[..count], &expected1);

        count = 0;
        for (_k, _v) in tree.range_iter(&50, &20) {
            results[count] = (*_k, _v);
            count += 1;
        }
        assert_eq!(count, 0);

        count = 0;
        for (k, v) in tree.range_iter(&5, &100) {
            results[count] = (*k, *v);
            count += 1;
        }
        let expected3 = [
            (10, "A"), (20, "B"), (30, "C"), (40, "D"),
            (50, "E"), (60, "F"), (70, "G")
        ];
        assert_eq!(&results[..count], &expected3);

        count = 0;
        for (k, v) in tree.range_iter(&30, &31) {
            results[count] = (*k, *v);
            count += 1;
        }
        let expected4 = [(30, "C")];
        assert_eq!(&results[..count], &expected4);

        count = 0;
        for (_k, _v) in tree.range_iter(&80, &90) {
            results[count] = (*_k, _v);
            count += 1;
        }
        assert_eq!(count, 0);
    }

    #[cfg(feature = "expanded")]
    #[test]
    fn test_stress_node_sizes_with_rotations_and_rebalance() {
        let mut tree = RedBlackTree::<i32, &str, 100>::new();

        for i in 1..=31 {
            tree.insert(i, "x");
            validate_node_sizes(&tree, tree.root);
        }

        for i in (1..=31).step_by(2) {
            tree.remove(i);
            validate_node_sizes(&tree, tree.root);
        }

        for i in (32..=63).rev() {
            tree.insert(i, "y");
            validate_node_sizes(&tree, tree.root);
        }

        for i in (2..=63).step_by(4) {
            tree.remove(i);
            validate_node_sizes(&tree, tree.root);
        }

        for &i in &[99, 77, 88, 66, 55, 44] {
            tree.insert(i, "z");
            validate_node_sizes(&tree, tree.root);
        }
    }

    #[cfg(feature = "expanded")]
    #[test]
    fn test_rank_function() {
        let mut tree = RedBlackTree::<i32, &str, 20>::new();

        let items = [10, 20, 5, 15, 25];
        for &item in &items {
            tree.insert(item, "v");
        }

        assert_eq!(tree.rank(&5), 0);  
        assert_eq!(tree.rank(&10), 1);
        assert_eq!(tree.rank(&15), 2);
        assert_eq!(tree.rank(&20), 3);
        assert_eq!(tree.rank(&25), 4);
        assert_eq!(tree.rank(&30), 5);
        assert_eq!(tree.rank(&13), 2);
        assert_eq!(tree.rank(&1), 0);
    }

    #[cfg(feature = "expanded")]
    #[test]
    fn test_select_function() {
        let mut tree = RedBlackTree::<i32, &str, 20>::new();

        let values = [10, 20, 5, 15, 25];
        for &v in &values {
            tree.insert(v, "val");
        }

        assert_eq!(tree.select(0), Some(&5));
        assert_eq!(tree.select(1), Some(&10));
        assert_eq!(tree.select(2), Some(&15));
        assert_eq!(tree.select(3), Some(&20));
        assert_eq!(tree.select(4), Some(&25));
        assert_eq!(tree.select(5), None); 
    }

    #[test]
    fn test_example() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();

        tree.insert(10, "A");
        tree.insert(20, "B");
        tree.insert(5, "C");

        tree.update(10, "Updated A");

        assert_eq!(tree.search(&10), Some(&"Updated A"));
        assert_eq!(tree.search(&20), Some(&"B"));
        assert_eq!(tree.search(&5), Some(&"C"));
        assert_eq!(tree.contains_key(&20), true);
        assert_eq!(tree.contains_key(&100), false);

        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some((&5, &"C")));
        assert_eq!(iter.next(), Some((&10, &"Updated A")));
        assert_eq!(iter.next(), Some((&20, &"B")));
        assert_eq!(iter.next(), None);

        assert_eq!(tree.remove(20), true);
        assert_eq!(tree.remove(20), false);
        assert_eq!(tree.search(&20), None);
        assert_eq!(tree.contains_key(&20), false);
    }

    #[test]
    fn test_utils() {
        let mut tree = setup_small_tree();
        assert_eq!(tree.contains_key(&10), true);
        assert_eq!(tree.get_mut(&10), Some(&mut "A"));
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.isEmpty(), false);
    }

    #[test]
    fn test_min_and_max() {
        let tree = setup_small_tree();
        assert_eq!(tree.min(), Some((&5, &"C")));
        assert_eq!(tree.max(), Some((&20, &"B")));
    }

    #[test]
    fn test_iter() {
        let tree = setup_small_tree();

        let mut iter = tree.iter();
        assert_eq!(iter.next(), Some((&5, &"C")));
        assert_eq!(iter.next(), Some((&10, &"A")));
    }

    #[test]
    fn test_insert_and_search() {
        let tree = setup_small_tree();
        assert_eq!(tree.search(&10), Some(&"A"));
        assert_eq!(tree.search(&20), Some(&"B"));
        assert_eq!(tree.search(&5), Some(&"C"));
        assert_eq!(tree.search(&30), None);
        assert!(tree.is_valid());
    }

    #[test]
    fn test_remove_leaf_node() {
        let mut tree = setup_small_tree();
        assert_eq!(tree.remove(5), true);
        assert_eq!(tree.remove(5), false);
        assert_eq!(tree.search(&5), None);
        assert_eq!(tree.search(&10), Some(&"A"));
        assert_eq!(tree.search(&20), Some(&"B"));
        assert!(tree.is_valid());
    }

    #[test]
    fn test_remove_node_with_one_child() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();
        tree.insert(10, "A");
        tree.insert(5, "B");
        tree.insert(2, "C");

        assert_eq!(tree.remove(5), true);
        assert_eq!(tree.remove(5), false);
        assert_eq!(tree.search(&5), None);
        assert_eq!(tree.search(&2), Some(&"C"));
        assert!(tree.is_valid());
    }

    #[test]
    fn test_remove_node_with_two_children() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();
        tree.insert(10, "A");
        tree.insert(5, "B");
        tree.insert(15, "C");
        tree.insert(12, "D");
        tree.insert(18, "E");

        assert_eq!(tree.remove(15), true);
        assert_eq!(tree.remove(15), false);
        assert_eq!(tree.search(&15), None);
        assert_eq!(tree.search(&12), Some(&"D"));
        assert_eq!(tree.search(&18), Some(&"E"));
        assert!(tree.is_valid());
    }

    #[test]
    fn test_reinsert_removed_key() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();
        tree.insert(42, "X");
        assert_eq!(tree.remove(42), true);
        assert_eq!(tree.remove(42), false);
        tree.insert(42, "Y");

        assert_eq!(tree.search(&42), Some(&"Y"));
        assert!(tree.is_valid());
    }

    #[test]
    fn test_multiple_insert_remove() {
        let mut tree = RedBlackTree::<i32, i32, 100>::new();

        for i in 0..100 {
            tree.insert(i, i * 10);
        }
        for i in 0..100 {
            assert_eq!(tree.search(&i), Some(&(i * 10)));
        }
        for i in 0..100 {
            assert_eq!(tree.remove(i), true);
            assert_eq!(tree.remove(i), false);
            assert_eq!(tree.search(&i), None);
        }
        assert!(tree.is_valid());
    }

    #[test]
    fn test_balanced_after_removal() {
        let mut tree = RedBlackTree::<i32, i32, 10>::new();
        for &k in &[50, 30, 70, 20, 40, 60, 80] {
            tree.insert(k, k);
        }

        assert_eq!(tree.remove(30), true);
        assert_eq!(tree.remove(70), true);
        assert_eq!(tree.remove(30), false);

        for &k in &[30, 70] {
            assert_eq!(tree.search(&k), None);
        }
        for &k in &[20, 40, 60, 80] {
            assert_eq!(tree.search(&k), Some(&k));
        }
        assert!(tree.is_valid());
    }

    #[test]
    fn test_random_insertion_and_removal() {
        use rand::{SeedableRng, rngs::SmallRng, prelude::SliceRandom};

        const COUNT: usize = 60;
        let mut rng = SmallRng::seed_from_u64(42);
        let mut keys = [0usize; COUNT];
        for (i, k) in keys.iter_mut().enumerate() {
            *k = i;
        }

        keys.shuffle(&mut rng);
        let mut tree = RedBlackTree::<usize, usize, COUNT>::new();

        for &k in &keys {
            tree.insert(k, k + 123);
        }
        for &k in &keys {
            assert_eq!(tree.search(&k), Some(&(k + 123)));
        }

        keys.shuffle(&mut rng);
        for &k in &keys {
            assert_eq!(tree.remove(k), true);
            assert_eq!(tree.remove(k), false);
            assert_eq!(tree.search(&k), None);
        }

        assert_eq!(tree.root, SENTINEL);
        assert!(tree.is_valid());
    }

    #[test]
    fn test_large_insertion_and_removal() {
        const COUNT: usize = 1_000;
        let mut tree = RedBlackTree::<usize, usize, COUNT>::new();

        for i in 0..COUNT {
            tree.insert(i, i);
        }
        for i in 0..COUNT {
            assert_eq!(tree.search(&i), Some(&i));
        }
        for i in 0..COUNT {
            assert_eq!(tree.remove(i), true);
            assert_eq!(tree.remove(i), false);
            assert_eq!(tree.search(&i), None);
        }

        assert_eq!(tree.root, SENTINEL);
        assert!(tree.is_valid());
    }

    #[test]
    fn test_descending_inserts_then_remove_half() {
        let mut tree = RedBlackTree::<i32, i32, 1_000>::new();

        for i in (0..1_000).rev() {
            tree.insert(i, i);
        }
        for i in 0..500 {
            assert_eq!(tree.remove(i), true);
            assert_eq!(tree.remove(i), false);
            assert_eq!(tree.search(&i), None);
        }
        for i in 500..1000 {
            assert_eq!(tree.search(&i), Some(&i));
        }
    }
}


