const SENTINEL: usize = usize::MAX;

#[derive(Debug, Eq, PartialEq)]
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

struct RedBlackTree<K: Ord, V> {
    nodes: Vec<Node<K,V>>,
    free_indexes: Vec<usize>,
    root: usize
}

impl<K: Ord,V> RedBlackTree<K,V> {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            free_indexes: Vec::new(),
            root: SENTINEL            
        }
    }

    fn insert(&mut self, z: (K,V)){
        let new_node = Node {
            key: z.0,
            value: z.1,
            color: Color::Red,
            parent: SENTINEL,
            left: SENTINEL,
            right: SENTINEL
        };
        let new_node_index = if let Some(free) = self.free_indexes.pop() {
            self.nodes[free] = new_node;
            free
        } else {
            self.nodes.push(new_node);
            self.nodes.len() - 1
        };

        let mut x = self.root;
        let mut y = SENTINEL;

        while x != SENTINEL {
            y = x;
            let y_node = &self.nodes[y];
            if self.nodes[new_node_index].key < y_node.key {
                x = y_node.left;
            }else{
                x = y_node.right;
            }
        }
        
        self.nodes[new_node_index].parent = y;
        
        if y == SENTINEL {
            self.root = new_node_index;
        } else if self.nodes[new_node_index].key < self.nodes[y].key {
            self.nodes[y].left = new_node_index;
        } else {
            self.nodes[y].right = new_node_index;
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
        let y_left_child = self.nodes[y].left;

        self.nodes[x].right = y_left_child;

        if y_left_child != SENTINEL {
            self.nodes[y_left_child].parent = x;
        }

        let x_parent = self.nodes[x].parent;
        self.nodes[y].parent = x_parent;

        if self.nodes[x].parent == SENTINEL {
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
}

fn main() {
    let mut rbtree = RedBlackTree::new();
    rbtree.insert(("Cara", 1));
    rbtree.insert(("Coroa", 2));
    rbtree.insert(("Árvore", 3));
    rbtree.insert(("Zebra", 4));
    rbtree.insert(("Laranja", 5));
    rbtree.insert(("Laranja2", 5));
    rbtree.insert(("Laranja3", 5));
    rbtree.insert(("Laranja4", 5));

    for (i, node) in rbtree.nodes.iter().enumerate() {
        println!("{}: {:?}", i, node);
    }

    println!("Raiz: {}", rbtree.root);
}
