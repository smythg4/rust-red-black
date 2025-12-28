use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::{Rc, Weak};

use anyhow::{Result, bail};

#[derive(Debug, Clone, Copy, PartialEq)]
enum Color {
    Red,
    Black,
}

type NodeRef<T> = Rc<RefCell<Node<T>>>;
type ParentRef<T> = Weak<RefCell<Node<T>>>;

struct Node<T> {
    key: T,
    color: Color,
    left: Option<NodeRef<T>>,
    right: Option<NodeRef<T>>,
    parent: Option<ParentRef<T>>,
}

impl<T> Node<T> {
    pub fn new(key: T) -> NodeRef<T> {
        Rc::new(RefCell::new(Node {
            key,
            color: Color::Red,
            left: None,
            right: None,
            parent: None,
        }))
    }
}

// Five properties of Red-Black Trees:
// 1. Every node is either red or black
// 2. The root is black
// 3. Every leaf (NIL) is black (we'll use None)
// 4. If a node is red, both its children are black (no two red nodes in a row)
// 5. For each node, all simple paths from node to descendant leaves contain the same
//    number of black nodes (black-height)

// These invariants guarantee that tree height is at most 2 * log(n), ensuring O(log n) operations
pub struct RBTree<T> {
    root: Option<NodeRef<T>>,
}

impl<T: Ord + Clone> RBTree<T> {
    pub fn new() -> Self {
        RBTree { root: None }
    }

    pub fn insert(&mut self, key: T) {
        let new_node = Node::new(key.clone());

        // case 1: empty tree
        if self.root.is_none() {
            new_node.borrow_mut().color = Color::Black; // root is always black (2)
            self.root = Some(new_node);
            return;
        }

        // case 2: tree has nodes
        let mut current = self.root.as_ref().unwrap().clone();

        loop {
            // determine direction
            let cmp = {
                let node = current.borrow();
                key.cmp(&node.key)
            };

            match cmp {
                Ordering::Equal => return,
                Ordering::Less => {
                    // go left
                    let left_child = current.borrow().left.clone();
                    match left_child {
                        Some(left) => current = left,
                        None => {
                            // 1. set new_node.parent = weak reference to current
                            // 2. Set current.left = new_node
                            // 3. Break
                            new_node.borrow_mut().parent = Some(Rc::downgrade(&current));
                            current.borrow_mut().left = Some(new_node.clone());
                            break;
                        }
                    }
                }
                Ordering::Greater => {
                    // go right
                    let right_child = current.borrow().right.clone();
                    match right_child {
                        Some(right) => current = right,
                        None => {
                            // 1. set new_node.parent = weak reference to current
                            // 2. Set current.right = new_node
                            // 3. Break
                            new_node.borrow_mut().parent = Some(Rc::downgrade(&current));
                            current.borrow_mut().right = Some(new_node.clone());
                            break;
                        }
                    }
                }
            }
        }

        self.insert_fixup(new_node).unwrap(); // will error if rotations are called incorrectly
    }

    fn search(&self, key: &T) -> bool {
        if self.root.is_none() {
            return false;
        }

        let mut current = self.root.as_ref().unwrap().clone();

        loop {
            let cmp = {
                let node = current.borrow();
                key.cmp(&node.key)
            };
            match cmp {
                Ordering::Equal => return true,
                Ordering::Less => {
                    let left = current.borrow().left.clone();
                    match left {
                        Some(node) => current = node,
                        None => return false,
                    }
                }
                Ordering::Greater => {
                    let right = current.borrow().right.clone();
                    match right {
                        Some(node) => current = node,
                        None => return false,
                    }
                }
            }
        }
    }

    fn rotate_left(&mut self, x: &NodeRef<T>) -> Result<()> {
        // step 1: get y (x's right child)
        let y = {
            let x_borrow = x.borrow();
            x_borrow
                .right
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("rotate_left: x must have right child"))?
                .clone()
        };

        // step 2: turn y's left subtree into x's right position
        let y_left = y.borrow().left.clone();
        x.borrow_mut().right = y_left.clone();

        // if y.left exists, update its parent to x
        if let Some(ref y_left_node) = y_left {
            y_left_node.borrow_mut().parent = Some(Rc::downgrade(x));
        }

        // step 3: link x's parent to y
        let x_parent = x.borrow().parent.clone();
        y.borrow_mut().parent = x_parent.clone();

        match x_parent {
            None => {
                // x was root, so y becomes new root
                self.root = Some(y.clone());
            }
            Some(ref parent_weak) => {
                if let Some(parent) = parent_weak.upgrade() {
                    // determine if x was left or right child
                    let x_was_left = {
                        let p = parent.borrow();
                        p.left
                            .as_ref()
                            .map(|left| Rc::ptr_eq(left, x))
                            .unwrap_or(false)
                    };

                    if x_was_left {
                        parent.borrow_mut().left = Some(y.clone());
                    } else {
                        parent.borrow_mut().right = Some(y.clone());
                    }
                }
            }
        }

        // step 4: put x on y's left
        y.borrow_mut().left = Some(x.clone());
        x.borrow_mut().parent = Some(Rc::downgrade(&y));

        Ok(())
    }

    fn rotate_right(&mut self, x: &NodeRef<T>) -> Result<()> {
        // step 1: get y (x's left child)
        let y = {
            let x_borrow = x.borrow();
            x_borrow
                .left
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("rotate_right: x must have left child"))?
                .clone()
        };

        // step 2: turn y's right subtree into x's left position
        let y_right = y.borrow().right.clone();
        x.borrow_mut().left = y_right.clone();

        // if y.right exists, update its parent to x
        if let Some(ref y_right_node) = y_right {
            y_right_node.borrow_mut().parent = Some(Rc::downgrade(x));
        }

        // step 3: link x's parent to y
        let x_parent = x.borrow().parent.clone();
        y.borrow_mut().parent = x_parent.clone();

        match x_parent {
            None => {
                // x was root, so y becomes new root
                self.root = Some(y.clone());
            }
            Some(ref parent_weak) => {
                if let Some(parent) = parent_weak.upgrade() {
                    // determine if x was left or right child
                    let x_was_left = {
                        let p = parent.borrow();
                        p.left
                            .as_ref()
                            .map(|left| Rc::ptr_eq(left, x))
                            .unwrap_or(false)
                    };

                    if x_was_left {
                        parent.borrow_mut().left = Some(y.clone());
                    } else {
                        parent.borrow_mut().right = Some(y.clone());
                    }
                }
            }
        }

        // step 4: put x on y's right
        y.borrow_mut().right = Some(x.clone());
        x.borrow_mut().parent = Some(Rc::downgrade(&y));

        Ok(())
    }

    fn get_parent(node: &NodeRef<T>) -> Option<NodeRef<T>> {
        node.borrow().parent.as_ref()?.upgrade()
    }

    fn get_grandparent(node: &NodeRef<T>) -> Option<NodeRef<T>> {
        let parent = Self::get_parent(node)?;
        Self::get_parent(&parent)
    }

    fn get_uncle(node: &NodeRef<T>) -> Option<NodeRef<T>> {
        let parent = Self::get_parent(node)?;
        let grandparent = Self::get_grandparent(node)?;

        let gp = grandparent.borrow();
        let parent_is_left = gp
            .left
            .as_ref()
            .map(|left| Rc::ptr_eq(left, &parent))
            .unwrap_or(false);

        if parent_is_left {
            gp.right.clone()
        } else {
            gp.left.clone()
        }
    }

    fn insert_fixup(&mut self, mut z: NodeRef<T>) -> Result<()> {
        // loop while parent exists and is red
        while let Some(parent) = Self::get_parent(&z) {
            if parent.borrow().color != Color::Red {
                break; // parent is black
            }

            // parent is red, get grandparent (must exists since root is black)
            let grandparent = if let Some(gp) = Self::get_grandparent(&z) {
                gp
            } else {
                break;
            };

            // determine if parent is left or right child of grandparent
            let parent_is_left = {
                let gp = grandparent.borrow();
                gp.left
                    .as_ref()
                    .map(|left| Rc::ptr_eq(left, &parent))
                    .unwrap_or(false)
            };

            let uncle = Self::get_uncle(&z);

            if parent_is_left {
                // parent is left child of grandparent

                // check uncle's color
                let uncle_is_red = uncle
                    .as_ref()
                    .map(|u| u.borrow().color == Color::Red)
                    .unwrap_or(false);

                if uncle_is_red {
                    // case 1: uncle is red - just recolor
                    parent.borrow_mut().color = Color::Black;
                    uncle.unwrap().borrow_mut().color = Color::Black;
                    grandparent.borrow_mut().color = Color::Red;
                    z = grandparent; // move up and continue
                } else {
                    // uncle is black

                    // check if z is right child of parent
                    let z_is_right_child = {
                        let p = parent.borrow();
                        p.right
                            .as_ref()
                            .map(|right| Rc::ptr_eq(right, &z))
                            .unwrap_or(false)
                    };

                    let mut parent_for_rotation = parent.clone();
                    if z_is_right_child {
                        // case 2: z is right child - rotate to make case 3
                        z = parent.clone();
                        self.rotate_left(&z)?;
                        parent_for_rotation = Self::get_parent(&z).unwrap();
                    }

                    // case 3: z is left child - rotate and recolor
                    let gp = Self::get_grandparent(&z).unwrap();
                    parent_for_rotation.borrow_mut().color = Color::Black;
                    gp.borrow_mut().color = Color::Red;
                    self.rotate_right(&gp)?;
                }
            } else {
                // parent is right child of grandparent

                // check uncle's color
                let uncle_is_red = uncle
                    .as_ref()
                    .map(|u| u.borrow().color == Color::Red)
                    .unwrap_or(false);

                if uncle_is_red {
                    // case 1: uncle is red - just recolor
                    parent.borrow_mut().color = Color::Black;
                    uncle.unwrap().borrow_mut().color = Color::Black;
                    grandparent.borrow_mut().color = Color::Red;
                    z = grandparent; // move up and continue
                } else {
                    // uncle is black

                    // check if z is left child of parent
                    let z_is_left_child = {
                        let p = parent.borrow();
                        p.left
                            .as_ref()
                            .map(|left| Rc::ptr_eq(left, &z))
                            .unwrap_or(false)
                    };

                    let mut parent_for_rotation = parent.clone();
                    if z_is_left_child {
                        // case 2: z is left child - rotate to make case 3
                        z = parent.clone();
                        self.rotate_right(&z)?;
                        parent_for_rotation = Self::get_parent(&z).unwrap();
                    }

                    // case 3: z is right child - rotate and recolor
                    let gp = Self::get_grandparent(&z).unwrap();
                    parent_for_rotation.borrow_mut().color = Color::Black;
                    gp.borrow_mut().color = Color::Red;
                    self.rotate_left(&gp)?;
                }
            }
        }

        // finally, make sure the root is black
        if let Some(ref root) = self.root {
            root.borrow_mut().color = Color::Black;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_insert_and_search() {
        let mut tree = RBTree::new();

        // Insert some values
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.insert(1);
        tree.insert(9);

        // Search for inserted values
        assert!(tree.search(&5));
        assert!(tree.search(&3));
        assert!(tree.search(&7));
        assert!(tree.search(&1));
        assert!(tree.search(&9));

        // Search for non-existent values
        assert!(!tree.search(&2));
        assert!(!tree.search(&10));
        assert!(!tree.search(&0));
    }

    #[test]
    fn test_empty_tree() {
        let tree: RBTree<i32> = RBTree::new();
        assert!(!tree.search(&5));
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = RBTree::new();
        tree.insert(5);
        tree.insert(5); // Duplicate
        assert!(tree.search(&5));
    }

    #[test]
    fn test_rotation() {
        let mut tree = RBTree::new();

        // Build a simple tree:
        //     5
        //    / \
        //   3   7
        //      / \
        //     6   9
        tree.insert(5);
        tree.insert(3);
        tree.insert(7);
        tree.insert(6);
        tree.insert(9);

        // All values should be findable
        assert!(tree.search(&5));
        assert!(tree.search(&3));
        assert!(tree.search(&7));
        assert!(tree.search(&6));
        assert!(tree.search(&9));

        // Rotate left at root (5)
        // Should become:
        //     7
        //    / \
        //   5   9
        //  / \
        // 3   6
        let root = tree.root.as_ref().unwrap().clone();
        tree.rotate_left(&root).unwrap();

        // All values still findable after rotation
        assert!(tree.search(&5));
        assert!(tree.search(&3));
        assert!(tree.search(&7));
        assert!(tree.search(&6));
        assert!(tree.search(&9));

        // Verify new root is 7
        let new_root = tree.root.as_ref().unwrap();
        assert_eq!(new_root.borrow().key, 7);
    }
}
