//! A tree-walk [`Interpreter`] for IMP programs.

use std::{
    collections::HashMap,
    convert::Infallible,
    hash::Hash,
    ops::{Add, Mul, Sub},
};

use crate::{ast::tree::Evaluator, parser::aexp::Aexp};

/// The state of an interpreter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State<V, T>(HashMap<V, T>)
where
    V: Hash + Eq;

impl<V, T> State<V, T>
where
    V: Hash + Eq,
{
    /// Returns the value of the given `var`, or `None` if it is unbound.
    pub fn get(&self, var: &V) -> Option<&T> {
        self.0.get(var)
    }
}

/// A tree-walk interpreter for IMP programs, which
/// executes programs by walking the tree, evaluating
/// expressions, and updating internal state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpreter<V, T>
where
    V: Hash + Eq,
{
    /// The internal state of the interpreter.
    state: State<V, T>,
}

impl<'s, V, T> Evaluator<&'s State<V, T>, Aexp<V, T>> for Interpreter<V, T>
where
    V: Hash + Eq,
    T: Clone + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    type Output = T;
    type Error = Infallible;

    fn evaluate(
        tree: Aexp<V, T>,
        state: &'s State<V, T>,
    ) -> Result<(Self::Output, &'s State<V, T>), Self::Error> {
        Ok((evaluate_aexp(state, tree), state))
    }
}

/// Evaluates the given `expr` based on some `state`.
fn evaluate_aexp<V, T>(state: &State<V, T>, expr: Aexp<V, T>) -> T
where
    V: Hash + Eq,
    T: Clone + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    match expr {
        Aexp::Int(int) => int,
        Aexp::Var(var) => state.get(&var).unwrap().clone(),
        Aexp::Add(lhs, rhs) => evaluate_aexp(state, *lhs) + evaluate_aexp(state, *rhs),
        Aexp::Mul(lhs, rhs) => evaluate_aexp(state, *lhs) * evaluate_aexp(state, *rhs),
        Aexp::Sub(lhs, rhs) => evaluate_aexp(state, *lhs) - evaluate_aexp(state, *rhs),
    }
}
