//! A tree-walk [`Interpreter`] for IMP programs.

use std::{
    collections::HashMap,
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

impl<V, T> Evaluator<&Aexp<V, T>> for &Interpreter<V, T>
where
    V: Hash + Eq,
    T: Clone + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    type Output = T;

    fn evaluate(self, tree: &Aexp<V, T>) -> Self::Output {
        match tree {
            Aexp::Int(int) => int.clone(),
            Aexp::Var(var) => self.state.get(var).unwrap().clone(),
            Aexp::Add(lhs, rhs) => self.evaluate(lhs) + self.evaluate(rhs),
            Aexp::Mul(lhs, rhs) => self.evaluate(lhs) * self.evaluate(rhs),
            Aexp::Sub(lhs, rhs) => self.evaluate(lhs) - self.evaluate(rhs),
        }
    }
}
