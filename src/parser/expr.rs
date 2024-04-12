//! Traits governing the behaviour of the distinct kinds of expressions.

use std::{collections::HashSet, hash::Hash};

/// A trait for expressions.
pub trait Expr {
    /// The type of the names/variables/idents in this expression.
    type Name: Eq + Hash;

    /// Returns a list of the names mentioned in `self`.
    fn names(&self) -> HashSet<&Self::Name>;
}
