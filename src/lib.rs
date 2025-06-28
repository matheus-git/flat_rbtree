use std::mem::MaybeUninit;

const SENTINEL: usize = usize::MAX;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, Copy)]
struct Node<K, V> {
    key: K,
    value: V,
    color: Color,
    parent: usize,
    left: usize,
    right: usize,
}

#[derive(Debug, Clone)]
pub struct RedBlackTree<K: Ord + Copy, V: Copy> {
    nodes: Vec<MaybeUninit<Node<K, V>>>,
    free_indexes: Vec<usize>,
    root: usize
}

impl<K: Ord + Copy, V: Copy> RedBlackTree<K,V> {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            free_indexes: Vec::new(),
            root: SENTINEL            
        }
    }

    pub fn search(&self, key: K) -> Option<&V> {
        if self.root == SENTINEL {
            return None;
        }

        let mut x = self.root;
        while x != SENTINEL {
            let node = unsafe { self.nodes[x].assume_init_ref() };

            if key == node.key {
                return Some(&node.value);
            }

            x = if key < node.key {
                node.left
            } else {
                node.right
            };
        }

        None
    }
    
    #[inline(always)]
    pub fn insert(&mut self, key: K, value: V) {
        let new_node = Node {
            key,
            value,
            color: Color::Red,
            parent: SENTINEL,
            left: SENTINEL,
            right: SENTINEL,
        };

        let new_node_index = if let Some(free) = self.free_indexes.pop() {
            self.nodes[free] = MaybeUninit::new(new_node);
            free
        } else {
            self.nodes.push(MaybeUninit::new(new_node));
            self.nodes.len() - 1
        };

        let mut x = self.root;
        let mut y = SENTINEL;

        while x != SENTINEL {
            y = x;
            let y_node = unsafe { self.nodes[y].assume_init_ref() };
            let new_key = unsafe { &self.nodes[new_node_index].assume_init_ref().key };
            if new_key < &y_node.key {
                x = y_node.left;
            } else {
                x = y_node.right;
            }
        }

        unsafe { self.nodes[new_node_index].assume_init_mut().parent = y };

        if y == SENTINEL {
            self.root = new_node_index;
        } else {
            unsafe {
                let new_key = &self.nodes[new_node_index].assume_init_ref().key;
                let y_node = self.nodes[y].assume_init_mut();

                if new_key < &y_node.key {
                    y_node.left = new_node_index;
                } else {
                    y_node.right = new_node_index;
                }
            }
        }

        self.insert_fixup(new_node_index);
    }

    fn insert_fixup(&mut self, mut z: usize) {
        while self.nodes[z].parent != SENTINEL && self.nodes[self.nodes[z].parent].color == Color::Red {
            let mut z_parent = self.nodes[z].parent;
            let mut z_grand = self.nodes[z_parent].parent;

            if z_parent == self.nodes[z_grand].left {
                let uncle = self.nodes[z_grand].right;
                if uncle != SENTINEL && self.nodes[uncle].color == Color::Red {
                    self.nodes[z_parent].color = Color::Black;
                    self.nodes[uncle].color = Color::Black;
                    self.nodes[z_grand].color = Color::Red;
                    z = z_grand;
                } else {
                    if z == self.nodes[z_parent].right {
                        z = z_parent;
                        z_parent = self.nodes[z].parent;
                        z_grand = self.nodes[z_parent].parent;
                        self.rotate_left(z);
                    }
                    if z_grand != SENTINEL {
                        self.nodes[z_parent].color = Color::Black;
                        self.nodes[z_grand].color = Color::Red;
                        self.rotate_right(z_grand);
                    }
                }
            } else {
                let uncle = self.nodes[z_grand].left;
                if uncle != SENTINEL && self.nodes[uncle].color == Color::Red {
                    self.nodes[z_parent].color = Color::Black;
                    self.nodes[uncle].color = Color::Black;
                    self.nodes[z_grand].color = Color::Red;
                    z = z_grand;
                } else {
                    if z == self.nodes[z_parent].left {
                        z = z_parent;
                        z_parent = self.nodes[z].parent;
                        z_grand = self.nodes[z_parent].parent;
                        self.rotate_right(z);
                    }
                    if z_grand != SENTINEL {
                        self.nodes[z_parent].color = Color::Black;
                        self.nodes[z_grand].color = Color::Red;
                        self.rotate_left(z_grand);
                    }
                }
            }
        }

        self.nodes[self.root].color = Color::Black;
    }

    fn rotate_left(&mut self, x: usize){
        let y = self.nodes[x].right;
        if y == SENTINEL {
            return;
        }
        let y_left_child = self.nodes[y].left;

        self.nodes[x].right = y_left_child;

        if y_left_child != SENTINEL {
            self.nodes[y_left_child].parent = x;
        }

        let x_parent = self.nodes[x].parent;
        self.nodes[y].parent = x_parent;

        if x_parent == SENTINEL {
            self.root = y;
        } else if x == self.nodes[x_parent].left {
            self.nodes[x_parent].left = y;
        } else {
            self.nodes[x_parent].right = y;
        }

        self.nodes[y].left = x;
        self.nodes[x].parent = y;
    }

    fn rotate_right(&mut self, x: usize) {
        let y = self.nodes[x].left;
        if y == SENTINEL {
            return;
        }
        let y_right_child = self.nodes[y].right;

        self.nodes[x].left = y_right_child;

        if y_right_child != SENTINEL {
            self.nodes[y_right_child].parent = x;
        }

        let x_parent = self.nodes[x].parent;
        self.nodes[y].parent = x_parent;

        if x_parent == SENTINEL {
            self.root = y;
        } else if x == self.nodes[x_parent].right {
            self.nodes[x_parent].right = y;
        } else {
            self.nodes[x_parent].left = y;
        }

        self.nodes[y].right = x;
        self.nodes[x].parent = y;
    }   

//    fn min(&self, mut x: usize) -> usize {
//        if x == SENTINEL {
//            return x
//        }
//        while self.nodes[x].left != SENTINEL {
//            x = self.nodes[x].left;
//        }
//        x
//    }
//
//    fn max(&self, mut x: usize) -> usize {
//        if x == SENTINEL {
//            return x
//        }
//        while self.nodes[x].right != SENTINEL {
//            x = self.nodes[x].right;
//        }
//        x
//    }
//
//    fn successor(&self, mut x: usize) -> usize {
//        if x == SENTINEL {
//            return x
//        }
//
//        if self.nodes[x].right != SENTINEL {
//            return self.min(self.nodes[x].right)
//        }
//        
//        let mut y = self.nodes[x].parent;
//
//        while y != SENTINEL && x == self.nodes[y].right {
//            x = y;
//            y = self.nodes[y].parent;
//        }
//        y
//    }
//
//    fn predecessor(&self, mut x: usize) -> usize {
//        if x == SENTINEL {
//            return x;
//        }
//
//        if self.nodes[x].left != SENTINEL {
//            return self.max(self.nodes[x].left);
//        }
//
//        let mut y = self.nodes[x].parent;
//
//        while y != SENTINEL && x == self.nodes[y].left {
//            x = y;
//            y = self.nodes[y].parent;
//        }
//
//        y
//    }
//
//    fn transplant(&mut self, u: usize, v: usize) {
//        if self.nodes[u].parent == SENTINEL {
//            self.root = v;
//        } else if u == self.nodes[self.nodes[u].parent].left {
//            let u_parent = self.nodes[u].parent;
//            self.nodes[u_parent].left = v;
//        } else {
//            let u_parent = self.nodes[u].parent;
//            self.nodes[u_parent].right = v;
//        }
//
//        if v != SENTINEL {
//            self.nodes[v].parent = self.nodes[u].parent;
//        }
//    }
//
//    pub fn remove(&mut self, key: K) {
//        let mut z = self.root;
//        while z != SENTINEL {
//            if key == self.nodes[z].key {
//                break;
//            } else if key < self.nodes[z].key {
//                z = self.nodes[z].left;
//            } else {
//                z = self.nodes[z].right;
//            }
//        }
//
//        if z == SENTINEL {
//            return;
//        }
//
//        let mut y = z;
//        let mut y_original_color = self.nodes[y].color;
//        let x: usize;
//
//        if self.nodes[z].left == SENTINEL {
//            x = self.nodes[z].right;
//            self.transplant(z, self.nodes[z].right);
//        } else if self.nodes[z].right == SENTINEL {
//            x = self.nodes[z].left;
//            self.transplant(z, self.nodes[z].left);
//        } else {
//            y = self.min(self.nodes[z].right);
//            y_original_color = self.nodes[y].color; 
//            x = self.nodes[y].right;
//            if y != self.nodes[z].right {
//                self.transplant(y, self.nodes[y].right);
//                self.nodes[y].right = self.nodes[z].right;
//                let y_right_child = self.nodes[y].right;
//                self.nodes[y_right_child].parent = y;
//            }
//
//            if x != SENTINEL {
//                self.nodes[x].parent = y;
//            }
//            self.transplant(z, y);
//            self.nodes[y].left = self.nodes[z].left;
//            let y_left_child = self.nodes[y].left;
//            self.nodes[y_left_child].parent = y;
//            self.nodes[y].color = self.nodes[z].color;
//        }
//
//        if y_original_color == Color::Black {
//            self.remove_fix(x);
//        }
//
//        self.free_indexes.push(z);
//    }
//
//    fn remove_fix(&mut self, mut x: usize) {
//        while x != self.root && x != SENTINEL && self.nodes[x].color == Color::Black {
//            let x_parent = self.nodes[x].parent;
//            if x == self.nodes[x_parent].left {
//                let mut cousin = self.nodes[x_parent].right;
//                if cousin == SENTINEL {
//                    x = x_parent;
//                    continue;
//                }
//                if self.is_red(cousin) {
//                    self.nodes[cousin].color = Color::Black;
//                    self.nodes[x_parent].color = Color::Red;
//                    self.rotate_left(x_parent);
//                    cousin = self.nodes[x_parent].right;
//                    if cousin == SENTINEL {
//                        x = x_parent;
//                        continue;
//                    }
//                }
//                
//                let cousin_left_child = self.nodes[cousin].left;
//                let mut cousin_right_child = self.nodes[cousin].right;
//                let left_black = cousin_left_child == SENTINEL || self.nodes[cousin_left_child].color == Color::Black;
//                let right_black = cousin_right_child == SENTINEL || self.nodes[cousin_right_child].color == Color::Black;
//
//                if left_black && right_black {
//                    self.nodes[cousin].color = Color::Red;
//                    x = x_parent
//                } else {
//                    if self.is_black(cousin_right_child) {
//                        self.nodes[cousin_left_child].color = Color::Black;
//                        self.nodes[cousin].color = Color::Red;
//                        self.rotate_right(cousin);
//                        cousin = self.nodes[x_parent].right;
//                        cousin_right_child = self.nodes[cousin].right;
//                    }
//                    self.nodes[cousin].color = self.nodes[x_parent].color;
//                    self.nodes[x_parent].color = Color::Black;
//                    self.nodes[cousin_right_child].color = Color::Black;
//                    self.rotate_left(x_parent);
//                    x = self.root;
//                }
//            }else {
//                let mut cousin = self.nodes[x_parent].left;
//                if cousin == SENTINEL {
//                    x = x_parent;
//                    continue;
//                }
//                if self.is_red(cousin) {
//                    self.nodes[cousin].color = Color::Black;
//                    self.nodes[x_parent].color = Color::Red;
//                    self.rotate_right(x_parent);
//                    cousin = self.nodes[x_parent].left;
//                    if cousin == SENTINEL {
//                        x = x_parent;
//                        continue;
//                    }
//                }
//                let mut cousin_left_child = self.nodes[cousin].left;
//                let cousin_right_child = self.nodes[cousin].right;
//                let left_black = cousin_left_child == SENTINEL || self.nodes[cousin_left_child].color == Color::Black;
//                let right_black = cousin_right_child == SENTINEL || self.nodes[cousin_right_child].color == Color::Black;
//
//                if left_black && right_black {
//                    self.nodes[cousin].color = Color::Red;
//                    x = x_parent
//                } else {
//                    if self.is_black(cousin_left_child) {
//                        self.nodes[cousin_right_child].color = Color::Black;
//                        self.nodes[cousin].color = Color::Red;
//                        self.rotate_left(cousin);
//                        cousin = self.nodes[x_parent].left;
//                        cousin_left_child = self.nodes[cousin].left;
//                    }
//                    self.nodes[cousin].color = self.nodes[x_parent].color;
//                    self.nodes[x_parent].color = Color::Black;
//                    self.nodes[cousin_left_child].color = Color::Black;
//                    self.rotate_right(x_parent);
//                    x = self.root;
//                }
//            }
//        }
//
//        if x != SENTINEL {
//            self.nodes[x].color = Color::Black;
//        }
//    }
//
//    fn is_black(&self, index: usize) -> bool {
//        index == SENTINEL || self.nodes[index].color == Color::Black
//    }
//
//    fn is_red(&self, index: usize) -> bool {
//        index != SENTINEL && self.nodes[index].color == Color::Red
//    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_search() {
        let mut tree = RedBlackTree::new();
        tree.insert(10, "A");
        tree.insert(20, "B");
        tree.insert(5, "C");

        assert_eq!(tree.search(10), Some(&"A"));
        assert_eq!(tree.search(20), Some(&"B"));
        assert_eq!(tree.search(5), Some(&"C"));
        assert_eq!(tree.search(30), None);
    }

    #[test]
    fn test_remove_leaf_node() {
        let mut tree = RedBlackTree::new();
        tree.insert(10, "A");
        tree.insert(5, "B");
        tree.insert(15, "C");

        tree.remove(5);
        assert_eq!(tree.search(5), None);
        assert_eq!(tree.search(10), Some(&"A"));
        assert_eq!(tree.search(15), Some(&"C"));
    }

    #[test]
    fn test_remove_node_with_one_child() {
        let mut tree = RedBlackTree::new();
        tree.insert(10, "A");
        tree.insert(5, "B");
        tree.insert(2, "C"); // left child of 5

        tree.remove(5);
        assert_eq!(tree.search(5), None);
        assert_eq!(tree.search(2), Some(&"C"));
    }

    #[test]
    fn test_remove_node_with_two_children() {
        let mut tree = RedBlackTree::new();
        tree.insert(10, "A");
        tree.insert(5, "B");
        tree.insert(15, "C");
        tree.insert(12, "D");
        tree.insert(18, "E");

        tree.remove(15);
        assert_eq!(tree.search(15), None);
        assert_eq!(tree.search(12), Some(&"D"));
        assert_eq!(tree.search(18), Some(&"E"));
    }

    #[test]
    fn test_reinsert_removed_key() {
        let mut tree = RedBlackTree::new();
        tree.insert(42, "X");
        assert_eq!(tree.search(42), Some(&"X"));

        tree.remove(42);
        assert_eq!(tree.search(42), None);

        tree.insert(42, "Y");
        assert_eq!(tree.search(42), Some(&"Y"));
    }

    #[test]
    fn test_multiple_insert_remove() {
        let mut tree = RedBlackTree::new();
        for i in 0..100 {
            tree.insert(i, i * 10);
        }

        for i in 0..100 {
            assert_eq!(tree.search(i), Some(&(i * 10)));
        }

        for i in 0..100 {
            tree.remove(i);
            assert_eq!(tree.search(i), None);
        }
    }

    #[test]
    fn test_root_is_black() {
        let mut tree = RedBlackTree::new();
        for i in [10, 20, 30, 5, 15] {
            tree.insert(i, i);
        }

        let root = tree.root;
        assert_eq!(tree.nodes[root].color, Color::Black);
    }

    #[test]
    fn test_balanced_after_removal() {
        let mut tree = RedBlackTree::new();
        for &k in &[50, 30, 70, 20, 40, 60, 80] {
            tree.insert(k, k);
        }

        tree.remove(30);
        tree.remove(70);
        assert_eq!(tree.search(30), None);
        assert_eq!(tree.search(70), None);
        assert_eq!(tree.search(20), Some(&20));
        assert_eq!(tree.search(40), Some(&40));
        assert_eq!(tree.search(60), Some(&60));
        assert_eq!(tree.search(80), Some(&80));
    }

    #[test]
    fn test_large_insertion_and_removal() {
        let mut tree = RedBlackTree::new();
        let count = 100_000;

        for i in 0..count {
            tree.insert(i, i);
        }

        for i in 0..count {
            assert_eq!(tree.search(i), Some(&i));
        }

        for i in 0..count {
            tree.remove(i);
            assert_eq!(tree.search(i), None);
        }

        assert_eq!(tree.root, SENTINEL);
    }

    #[test]
    fn test_invariant_red_black_properties() {
        fn count_black_height(tree: &RedBlackTree<i32, i32>, node_idx: usize) -> Option<usize> {
            if node_idx == SENTINEL {
                return Some(1);
            }
            let node = &tree.nodes[node_idx];
            let left = count_black_height(tree, node.left)?;
            let right = count_black_height(tree, node.right)?;
            if left != right {
                return None;
            }
            let is_black = node.color == Color::Black;
            Some(left + if is_black { 1 } else { 0 })
        }

        let mut tree = RedBlackTree::new();
        for i in 0..10_000 {
            tree.insert(i, i);
        }

        assert_ne!(tree.root, SENTINEL);
        assert_eq!(tree.nodes[tree.root].color, Color::Black);

        fn validate(tree: &RedBlackTree<i32, i32>, idx: usize) -> bool {
            if idx == SENTINEL {
                return true;
            }
            let node = &tree.nodes[idx];
            if node.color == Color::Red {
                if node.left != SENTINEL && tree.nodes[node.left].color == Color::Red {
                    return false;
                }
                if node.right != SENTINEL && tree.nodes[node.right].color == Color::Red {
                    return false;
                }
            }
            validate(tree, node.left) && validate(tree, node.right)
        }

        assert!(validate(&tree, tree.root));
        assert!(count_black_height(&tree, tree.root).is_some());
    }

    #[test]
    fn test_descending_inserts_then_remove_half() {
        let mut tree = RedBlackTree::new();

        for i in (0..10_000).rev() {
            tree.insert(i, i);
        }

        for i in 0..5_000 {
            tree.remove(i);
            assert_eq!(tree.search(i), None);
        }

        for i in 5_000..10_000 {
            assert_eq!(tree.search(i), Some(&i));
        }
    }
}
