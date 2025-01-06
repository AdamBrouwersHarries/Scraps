#![allow(dead_code)]

use std::collections::VecDeque;

#[derive(Clone, Debug)]
struct Tree<X> {
    pub val: X,
    pub ls: Vec<Tree<X>>,
}

impl<X> Tree<X> {
    pub fn b(val: X, ls: Vec<Tree<X>>) -> Self {
        Tree { val, ls }
    }

    pub fn l(val: X) -> Self {
        Tree { val, ls: vec![] }
    }

    pub fn ls(val: X, other: Vec<X>) -> Self {
        Tree {
            val,
            ls: other.into_iter().map(|v| Tree::l(v)).collect(),
        }
    }

    pub fn dfs<'tree>(&'tree self) -> DFSIter<'tree, X> {
        DFSIter::<'tree, X>::from_tree(self)
    }

    pub fn sfs<'tree>(&'tree self) -> SFSIter<'tree, X> {
        SFSIter::<'tree, X>::from_tree(self)
    }
}

struct DFSIter<'tree, X> {
    stack: Vec<&'tree Tree<X>>,
}

impl<'tree, X> DFSIter<'tree, X> {
    pub fn from_tree(t: &'tree Tree<X>) -> Self {
        DFSIter { stack: vec![t] }
    }
}

impl<'tree, X> Iterator for DFSIter<'tree, X> {
    type Item = &'tree X;

    fn next(&mut self) -> Option<Self::Item> {
        // Get the value from the top of the stack
        // If there's no value, then we're done iterating
        let t: &'tree Tree<X> = self.stack.pop()?;
        // Push the children from right to left onto the stack
        t.ls.iter().rev().for_each(|t| self.stack.push(&t));
        // Yield the result
        Some(&t.val)
    }
}

struct SFSIter<'tree, X> {
    stack: VecDeque<&'tree Tree<X>>,
}

impl<'tree, X> SFSIter<'tree, X> {
    pub fn from_tree(t: &'tree Tree<X>) -> Self {
        SFSIter {
            stack: vec![t].into(),
        }
    }
}

impl<'tree, X> Iterator for SFSIter<'tree, X> {
    type Item = &'tree X;

    fn next(&mut self) -> Option<Self::Item> {
        // Get the value from the top of the stack
        // If there's no value, then we're done iterating
        let t: &'tree Tree<X> = self.stack.pop_front()?;
        // Push the children from right to left onto the stack
        t.ls.iter().for_each(|t| self.stack.push_back(&t));
        // Yield the result
        Some(&t.val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tree_print() {
        let t = Tree::b(
            "1",
            vec![
                Tree::b("2", vec![Tree::ls("4", vec!["5", "6", "7"])]),
                Tree::b("3", vec![]),
            ],
        );

        println!("Tree: {:?}", t);

        println!("DFS: ");
        for v in t.dfs() {
            println!("{:?}", v);
        }

        println!("SFS: ");
        for v in t.sfs() {
            println!("{:?}", v);
        }
    }
}
