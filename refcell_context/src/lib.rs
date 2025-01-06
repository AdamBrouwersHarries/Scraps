#![allow(unused)]

use std::cell::Cell;

pub fn mutate_cell<T, F>(cell: &Cell<T>, f: F) -> ()
where
    F: Fn(&mut T) -> (),
    T: Default,
{
    let mut t = cell.take();
    f(&mut t);
    cell.set(t);
}


pub fn use_cell<T, F>(cell: &Cell<T>, f: F) -> () 
where 
F : Fn(&T) -> (), 
T: Default, 
{
    let t = cell.take();
    f(&t);
    cell.set(t);
}

// This should let us iterate over one vector, while mutating the other
struct VectorPair<T> {
    pub left: Cell<Vec<T>>,
    pub right: Cell<Vec<T>>,
}

impl<T: Clone> VectorPair<T> {
    pub fn init(left: Vec<T>, right: Vec<T>) -> Self {
        VectorPair {
            left: Cell::new(left),
            right: Cell::new(right),
        }
    }

    pub fn append_left(&self, v: T) -> () {
        mutate_cell(&self.left, |e: &mut Vec<T>| {
            e.push(v.clone());
        });
    }

    pub fn append_right(&self, v: T) -> () {
        mutate_cell(&self.right, |e: &mut Vec<T>| {
            e.push(v.clone());
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let l = vec![1,2,3,4,5];
        let r = vec![6,7,8,9,10];
        let vp = VectorPair::init(l, r);
        println!("Run: ");
        use_cell(&vp.left, |v| {
            for e in v.iter() {
                println!("{:?}", e);
                mutate_cell(&vp.right, |vr| { 
                    vr.push(*e);
                    mutate_cell(&vp.left, |vl| { 
                        vl.push(*e);
                    });
                });
            }
        });
        
        println!("Right: ");
        use_cell(&vp.right, |v| {
            for e in v.iter() {
                println!("{:?}", e);
            }
        });

        println!("Left: ");
        use_cell(&vp.left, |v| {
            for e in v.iter() {
                println!("{:?}", e);
            }
        });
    }
}
