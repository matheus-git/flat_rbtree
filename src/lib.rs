#![allow(warnings)]
#![cfg_attr(not(test), no_std)]

//! A fast, index-based Red-Black Tree with no heap allocations.
//!
//! ## Features
//! - No heap allocation
//! - All nodes are stored in a `array`, avoiding pointers
//! - Flat storage using `MaybeUninit`
//! - Suitable for `no_std` environments
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
}

pub struct RedBlackTreeIter<'a, K: Ord + 'a, V: 'a, const N: usize> {
    tree: &'a RedBlackTree<K, V, N>,
    index: usize,
}

impl<'a, K: Ord + 'a, V: 'a, const N: usize> Iterator for RedBlackTreeIter<'a, K, V, N> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == SENTINEL {
            let next = self.tree.min(self.tree.root);
            if next == SENTINEL {
                return None;
            }
            self.index = next;
            let next_node = self.tree.get_node_by_index(next);
            return Some((&next_node.key, &next_node.value))

        }
        let next = self.tree.successor(self.index);
        if next == SENTINEL {
            return None;
        }
        self.index = next;
        let next_node = self.tree.get_node_by_index(next);
        return Some((&next_node.key, &next_node.value))
    }
}

impl<'a, K: Ord + 'a, V: 'a, const N: usize> DoubleEndedIterator for RedBlackTreeIter<'a, K, V, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index == SENTINEL {
            let next = self.tree.max(self.tree.root);
            if next == SENTINEL {
                return None;
            }
            self.index = next;
            let next_node = self.tree.get_node_by_index(next);
            return Some((&next_node.key, &next_node.value))

        }
        let next = self.tree.predecessor(self.index);
        if next == SENTINEL {
            return None;
        }
        self.index = next;
        let next_node = self.tree.get_node_by_index(next);
        return Some((&next_node.key, &next_node.value))
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

    pub fn iter(&self) -> RedBlackTreeIter<'_, K, V, N> {
        RedBlackTreeIter {
            tree: self,
            index: SENTINEL,
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
    ///
    /// Panics if the tree is already full (`N` elements).
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
    /// If the key does not exist, this function does nothing.
    ///
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
    } 

    fn min_item(&self) -> Option<(&K, &V)> {
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

    fn max_item(&self) -> Option<(&K, &V)> {
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

    fn min(&self, mut x: usize) -> usize {
        if x == SENTINEL {
            return x
        }
        while self.get_node_by_index(x).left != SENTINEL {
            x = self.get_node_by_index(x).left;
        }
        x
    }

    fn max(&self, mut x: usize) -> usize {
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
            return self.min(self.get_node_by_index(x).right)
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
            return self.max(self.get_node_by_index(x).left);
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
        if self.get_node_by_index(u).parent == SENTINEL {
            self.root = v;
        } else if u == self.get_node_by_index(self.get_node_by_index(u).parent).left {
            let u_parent = self.get_node_by_index(u).parent;
            self.get_mut_node_by_index(u_parent).left = v;
        } else {
            let u_parent = self.get_node_by_index(u).parent;
            self.get_mut_node_by_index(u_parent).right = v;
        }

        if v != SENTINEL {
            self.get_mut_node_by_index(v).parent = self.get_node_by_index(u).parent;
        }
    }

    // Removes a key (and its associated value) from the tree.
    ///
    /// If the key is not found, nothing happens.
    #[inline(always)]
    pub fn remove(&mut self, key: K) {
        let mut z = self.get_index_by_key(&key);
        if z == SENTINEL {
            return;
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
            y = self.min(z_right);
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
        }

        if y_original_color == Color::Black {
            self.remove_fix(x);
        }

        self.free_indexes[self.free_len] = z;
        self.free_len += 1;
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

    #[test]
    fn test_min_and_max() {
        let tree = setup_small_tree();
        assert_eq!(tree.min_item(), Some((&5, &"C")));
        assert_eq!(tree.max_item(), Some((&20, &"B")));
    }   
    
    #[test]
    fn test_iter() {
        let tree = setup_small_tree();

        for pair in tree.iter() {
        }

        for pair in tree.iter().rev() {
        }
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
        tree.remove(5);
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

        tree.remove(5);
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

        tree.remove(15);
        assert_eq!(tree.search(&15), None);
        assert_eq!(tree.search(&12), Some(&"D"));
        assert_eq!(tree.search(&18), Some(&"E"));
        assert!(tree.is_valid());
    }

    #[test]
    fn test_reinsert_removed_key() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();
        tree.insert(42, "X");
        tree.remove(42);
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
            tree.remove(i);
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

        tree.remove(30);
        tree.remove(70);

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
            tree.remove(k);
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
            tree.remove(i);
            assert_eq!(tree.search(&i), None);
        }

        assert_eq!(tree.root, SENTINEL);
        assert!(tree.is_valid());
    }

    #[test]
    fn test_descending_inserts_then_remove_half() {
        let mut tree = RedBlackTree::<i32, i32, 10_000>::new();

        for i in (0..10_000).rev() {
            tree.insert(i, i);
        }
        for i in 0..5_000 {
            tree.remove(i);
            assert_eq!(tree.search(&i), None);
        }
        for i in 5_000..10_000 {
            assert_eq!(tree.search(&i), Some(&i));
        }
    }

    #[test]
    fn test_update_behavior() {
        let mut tree = RedBlackTree::<i32, &str, 10>::new();

        tree.update(42, "original");
        tree.update(42, "updated");
        tree.update(100, "new");

        assert_eq!(tree.search(&42), Some(&"updated"));
        assert_eq!(tree.search(&100), Some(&"new"));
        assert!(tree.is_valid());
    }
}


