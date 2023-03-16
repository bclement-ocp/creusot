extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        true
    }
}

pub fn id(x: WithInvariant) -> WithInvariant {
    x
}
