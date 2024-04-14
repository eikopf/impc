//! A tree-walk [`Interpreter`] for IMP programs.

use std::{
    collections::HashMap,
    hash::Hash,
    ops::{Add, BitAnd, BitOr, Deref, Mul, Not, Sub},
};

use thiserror::Error;

use crate::{
    parser::{aexp::Aexp, bexp::Bexp, cmd::Cmd},
    tree::Evaluator,
};

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

    fn eval(self, tree: &Aexp<V, T>) -> Self::Output {
        match tree {
            Aexp::Int(int) => Ok(int.clone()),
            Aexp::Var(var) => match self.state.get(var) {
                Some(int) => Ok(int.clone()),
                None => Err(VariableBindingError(vec![var.clone()])),
            },
            Aexp::Add(lhs, rhs) => join(self.eval(lhs.deref()), Add::add, self.eval(rhs.deref())),
            Aexp::Mul(lhs, rhs) => join(self.eval(lhs.deref()), Mul::mul, self.eval(rhs.deref())),
            Aexp::Sub(lhs, rhs) => join(self.eval(lhs.deref()), Sub::sub, self.eval(rhs.deref())),
        }
    }
}

impl<V, T> Evaluator<&Bexp<V, T>> for &Interpreter<V, T>
where
    V: Clone + Hash + Eq,
    T: Clone + Eq + Ord + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    type Output = Result<bool, VariableBindingError<V>>;

    fn eval(self, tree: &Bexp<V, T>) -> Self::Output {
        match tree {
            Bexp::Atom(atom) => Ok(*atom),
            Bexp::Eq(lhs, rhs) => join(self.eval(lhs), |a, b| a == b, self.eval(rhs)),
            Bexp::LessThan(lhs, rhs) => join(self.eval(lhs), |a, b| a < b, self.eval(rhs)),
            Bexp::GreaterThan(lhs, rhs) => join(self.eval(lhs), |a, b| a > b, self.eval(rhs)),
            Bexp::Not(inner) => self.eval(inner.deref()).map(Not::not),
            Bexp::And(lhs, rhs) => join(
                self.eval(lhs.deref()),
                BitAnd::bitand,
                self.eval(rhs.deref()),
            ),
            Bexp::Or(lhs, rhs) => {
                join(self.eval(lhs.deref()), BitOr::bitor, self.eval(rhs.deref()))
            }
        }
    }
}

impl<V, T> Evaluator<&Cmd<V, T>> for Interpreter<V, T>
where
    V: Clone + Hash + Eq,
    T: Clone + Eq + Ord + Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    type Output = Result<State<V, T>, VariableBindingError<V>>;

    fn eval(mut self, tree: &Cmd<V, T>) -> Self::Output {
        match tree {
            Cmd::Skip => Ok(self.state),
            Cmd::Assign(var, expr) => {
                let rhs = (&self).eval(expr)?;
                let _ = self.state.0.insert(var.clone(), rhs);
                Ok(self.state)
            }
            Cmd::Seq(first, second) => {
                let state = self.eval(first)?;
                self = Interpreter { state };
                self.eval(second)
            }
            Cmd::If {
                cond,
                true_case,
                false_case,
            } => match (&self).eval(cond)? {
                true => self.eval(true_case),
                false => self.eval(false_case),
            },
            Cmd::While(cond, body) => {
                while (&self).eval(cond)? {
                    let state = self.eval(body)?;
                    self = Interpreter { state };
                }

                Ok(self.state)
            }
        }
    }
}

impl<V, T> From<HashMap<V, T>> for Interpreter<V, T>
where
    V: Hash + Eq,
{
    fn from(value: HashMap<V, T>) -> Self {
        Interpreter {
            state: State(value),
        }
    }
}

/// A simple combinator to map `op` over a pair of results iff
/// they are both `Ok`, and to unify their errors otherwise.
///
/// > Effectively monadic-do for `Result<T, VariableBindingError<V>>`.
fn join<V, T, U>(
    lhs: Result<T, VariableBindingError<V>>,
    op: fn(T, T) -> U,
    rhs: Result<T, VariableBindingError<V>>,
) -> Result<U, VariableBindingError<V>> {
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

#[cfg(test)]
mod tests {
    use crate::{ast::Ast, int::ImpSize, lexer::token::Tokens, parser::aexp::aexp, tree::Tree};

    use super::*;

    #[test]
    fn check_aexp_evaluator_impl() {
        // state: { X => 4, Y => 0 }
        let interpreter: Interpreter<&str, ImpSize> = {
            let mut bindings = HashMap::new();
            bindings.insert("X", 4.into());
            bindings.insert("Y", 0.into());
            Interpreter {
                state: State(bindings),
            }
        };

        // expr: (* (- X 2) 12)
        let tokens: Tokens<_> = "(X - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_slice()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = (&interpreter).eval(&expr);
        eprintln!("evaluation: expr = {}", result.clone().unwrap());
        assert_eq!(result.unwrap(), ImpSize::from(24));

        // expr: (* (- Y 2) 12)
        let tokens: Tokens<_> = "(Y - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_slice()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = (&interpreter).eval(&expr);
        eprintln!("evaluation: expr = {}", result.clone().unwrap());
        assert_eq!(result.unwrap(), 0.into());

        // expr: (* (- Z 2) 12)
        // Z is unbound, so this should be an error
        let tokens: Tokens<_> = "(Z - 2) * 12".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_slice()).unwrap();
        eprintln!("parsed expr {expr}");
        let result = (&interpreter).eval(&expr);
        eprintln!("encountered error: {}", result.clone().unwrap_err());
        assert_eq!(result.unwrap_err(), VariableBindingError(vec!["Z"]));
    }

    #[test]
    fn check_complete_evaluator_impl() {
        let interpreter: Interpreter<_, ImpSize> = {
            let mut bindings = HashMap::new();
            bindings.insert("X", 0.into());
            Interpreter {
                state: State(bindings),
            }
        };

        let program = r#"
            X := 1; 
            Y := 7; 
            Z := 9; 
            if (false or X = 3) then 
                skip; 
                Z := 2 
            else 
                Z := 1 
            fi
        "#;

        let tokens = Tokens::<_, ImpSize>::try_from(program).unwrap();
        let ast = Ast::try_from(tokens.as_slice()).unwrap();
        eprintln!("ast:\n{}", ast.clone().root());

        let result = ast.map(|root| interpreter.eval(&root));
        assert!(result.is_ok_and(|state| {
            state.get(&"X").is_some_and(|&x| x == 1.into())
                && state.get(&"Y").is_some_and(|&y| y == 7.into())
                && state.get(&"Z").is_some_and(|&z| z == 1.into())
        }));
    }
}
