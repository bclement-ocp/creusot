// extern crate creusot_contracts;

// use creusot_contracts::*;

struct Item<A> {
    opt: Option<A>,
}

pub struct IterMut<'a, A: 'a> {
    blah: &'a mut A,
    inner: Item<&'a mut A>,
}

fn omg<'a, T>(t: IterMut<'a, T>) {}