#![allow(dead_code)]

mod util;

use std::cell::Cell;
use std::cmp::max;
use std::cmp::min;
use std::fmt;
use std::{
    fmt::{Debug, Display},
    rc::Rc,
};
use util::shift_vec;

#[derive(Debug)]
pub struct DragUpdate {
    pub from: usize,
    pub to: usize,
}

#[derive(Debug, PartialEq)]
pub struct Selectable<T: Debug + Display> {
    // A selectable element needs to have a value
    value: T,
    // And it needs to know where it lives in the list of selections
    selected: Cell<Option<usize>>,
    // It *doesn't* need to know where it lives in the list of sources, as we
    // can do that with a reference
}

impl<T> fmt::Display for Selectable<T>
where
    T: Debug + Display,
{
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.selected.get() {
            Some(i) => write!(f, "<{}, {}>", self.value, i),
            None => write!(f, "<{}, _>", self.value),
        }
    }
}

impl<T> Selectable<T>
where
    T: Debug + Display,
{
    pub fn from(value: T) -> Self {
        Selectable {
            value,
            selected: None.into(),
        }
    }

    pub fn rc_from(value: T) -> Rc<Self> {
        Rc::new(Self::from(value))
    }
}

#[derive(Debug)]
pub struct PickList<T: Debug + Display> {
    source: Vec<Rc<Selectable<T>>>,
    selected: Vec<Rc<Selectable<T>>>,
}

impl<T> fmt::Display for PickList<T>
where
    T: Debug + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write the source values:
        write!(f, "Source: [\n")?;
        for s in &self.source {
            write!(f, "  ")?;
            std::fmt::Display::fmt(&s, f)?;
            write!(f, "\n")?;
        }
        write!(f, "]\n")?;
        // Write the selected values:
        write!(f, "Selected: [\n")?;
        for (i, s) in self.selected.iter().enumerate() {
            write!(f, "  {}: ", i)?;
            std::fmt::Display::fmt(&s, f)?;
            write!(f, "\n")?;
        }
        write!(f, "]\n")
    }
}

impl<T> PickList<T>
where
    T: Debug + Display + std::cmp::PartialEq,
{
    pub fn from_vec(s: Vec<T>) -> Self {
        let l = s.len();
        PickList {
            source: s.into_iter().map(Selectable::rc_from).collect(),
            selected: Vec::with_capacity(l),
        }
    }

    // "Pick" a value from source
    pub fn select(&mut self, ix: usize) -> () {
        debug_assert!(ix < self.source.len());
        // get the source value at ix
        let v = &self.source[ix];
        if v.selected.get().is_some() {
            return;
        }
        // push it into selected
        self.selected.push(Rc::clone(&v));
        // Update the index in v
        v.selected.set(Some(self.selected.len() - 1));
        self.check_invariants();
    }

    // Deselect a value from selected
    pub fn deselect(&mut self, ix: usize) -> () {
        debug_assert!(ix < self.selected.len());
        self.selected[ix].selected.set(None);
        self.selected.remove(ix);
        for i in ix..self.selected.len() {
            self.selected[i].selected.set(Some(i));
        }
        self.check_invariants();
    }

    pub fn selected(&self) -> usize {
        self.selected.len()
    }

    pub fn update_selected(&mut self, update: DragUpdate) -> () {
        shift_vec(update.from, update.to, &mut self.selected);
        // We need to iterate over all the elements between from/to, and
        // update the "source array"'s index so that it correctly points to
        // them again. 
        if update.from < update.to {
            // If from < to, then everything from `from` to `to - 1` will need
            // to be updated, as `to` will implicitly "move down" in the
            // array.
            for i in update.from..update.to {
                self.selected[i].selected.set(Some(i));
            }
        } else {
            // If from > to, then `to` remains constant, but `from` will be
            // moved up one place in the array.
            for i in update.to..update.from + 1 {
                self.selected[i].selected.set(Some(i));
            }
        }
        self.check_invariants();
    }

    #[cfg(not(debug_assertions))]
    pub fn check_invariants(&self) -> () {
        // stub
    }

    #[cfg(debug_assertions)]
    pub fn check_invariants(&self) -> () {
        // Assert that all the elements of the selected are in the correct position
        for (i, e) in self.selected.iter().enumerate() {
            debug_assert!(e.selected.get().is_some());
            debug_assert_eq!(i, e.selected.get().unwrap());
        }

        // Assert that every element in the source array actually indexes correctly
        for e in self.source.iter() {
            match e.selected.get() {
                Some(i) => {
                    debug_assert!(i < self.source.len());
                    // get the value in the selected array
                    let other = &self.selected[i];
                    debug_assert_eq!(e, other);
                }
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng; // 0.8.5

    #[test]
    fn random_operations() {
        let source_size: usize = 2048;
        let source: Vec<u32> = (0..2048).collect();
        let mut s = PickList::from_vec(source);

        for _i in 0..(2 << 14) {
            let op = rand::thread_rng().gen_range(0..3);
            match op {
                0 => {
                    // Set one of the values
                    let ix: usize = rand::thread_rng().gen_range(0..source_size);
                    s.select(ix);
                }
                1 => {
                    // Deslect one of the values
                    let selcount = s.selected();
                    if selcount > 0 {
                        let ix: usize = rand::thread_rng().gen_range(0..selcount);
                        s.deselect(ix);
                    }
                }
                2 => {
                    // Move a value
                    let selcount = s.selected();
                    if selcount > 0 {
                        let from: usize = rand::thread_rng().gen_range(0..selcount);
                        let to: usize = rand::thread_rng().gen_range(0..selcount);
                        s.update_selected(DragUpdate { from, to });
                    }
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }

    #[test]
    fn deliberate() {
        let mut s = PickList::from_vec(vec!["A", "B", "C", "D", "E"]);
        s.select(2);
        s.select(4);
        s.select(1);
        s.update_selected(DragUpdate { from: 2, to: 1 });
        s.update_selected(DragUpdate { from: 0, to: 1 });
        s.update_selected(DragUpdate { from: 2, to: 0 });
    }
}
