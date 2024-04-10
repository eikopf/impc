//! A tree-walk [`Interpreter`] for IMP programs.

use std::{
    collections::HashMap,
    hash::Hash,
    ops::{Add, Mul, Sub},
};

use thiserror::Error;

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

/// The error type produced by an [`Interpreter`] when
/// attempting to read unbound variables while evaluating
/// arithmetic expressions.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[error("The following variables are unbound: {0:?}")]
pub struct VariableBindingError<V>(Vec<V>);

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
    V: Clone + Hash + Eq,
    T: Clone + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    type Output = Result<T, VariableBindingError<V>>;

    fn evaluate(self, tree: &Aexp<V, T>) -> Self::Output {
        // simple combinator to do `lhs op rhs` if both
        // are ok, or to propagate errors if at least one
        // is an error. god i wish rust had monads
        fn join<V, T>(
            lhs: Result<T, VariableBindingError<V>>,
            op: fn(T, T) -> T,
            rhs: Result<T, VariableBindingError<V>>,
        ) -> Result<T, VariableBindingError<V>> {
            match (lhs, rhs) {
                (Ok(lhs), Ok(rhs)) => Ok(op(lhs, rhs)),
                (Ok(_), Err(err)) => Err(err),
                (Err(err), Ok(_)) => Err(err),
                (Err(mut err1), Err(mut err2)) => {
                    err1.0.append(&mut err2.0);
                    Err(err1)
                }
            }
        }

        match tree {
            Aexp::Int(int) => Ok(int.clone()),
            Aexp::Var(var) => match self.state.get(var) {
                Some(int) => Ok(int.clone()),
                None => Err(VariableBindingError(vec![var.clone()])),
            },
            Aexp::Add(lhs, rhs) => join(self.evaluate(lhs), Add::add, self.evaluate(rhs)),
            Aexp::Mul(lhs, rhs) => join(self.evaluate(lhs), Mul::mul, self.evaluate(rhs)),
            Aexp::Sub(lhs, rhs) => join(self.evaluate(lhs), Sub::sub, self.evaluate(rhs)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{int::ImpSize, lexer::token::Tokens, parser::aexp::aexp, var::Var};

    use super::*;

    #[test]
    fn check_aexp_evaluator_impl() {
        // state: { X => 4, Y => 0 }
        let interpreter: Interpreter<Var, ImpSize> = {
            let mut bindings = HashMap::new();
            bindings.insert(Var::from("X"), 4.into());
            bindings.insert(Var::from("Y"), 0.into());
            Interpreter { state: State(bindings) }
        };

        // expr: (* (- X 2) 12)
        let tokens: Tokens = "(X - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<Var>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = interpreter.evaluate(&expr);
        eprintln!("evaluation: expr = {}", result.clone().unwrap());
        assert_eq!(result.unwrap(), 24.into());

        // expr: (* (- Y 2) 12)
        let tokens: Tokens = "(Y - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<Var>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = interpreter.evaluate(&expr);
        eprintln!("evaluation: expr = {}", result.clone().unwrap());
        assert_eq!(result.unwrap(), 0.into());

        // expr: (* (- Z 2) 12)
        // Z is unbound, so this should be an error
        let tokens: Tokens = "(Z - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<Var>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = interpreter.evaluate(&expr);
        eprintln!("encountered error: {}", result.clone().unwrap_err());
        assert_eq!(result.unwrap_err(), VariableBindingError(vec![Var::from("Z")]));
    }
}
