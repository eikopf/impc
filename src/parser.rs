//! A [`nom`]-based parser operating on sequences of tokens.
//!
//! # Expressions
//! IMP defines two distinct kinds of expressions: _arithmetic_ and _boolean_. These
//! have been reified into the [`aexp::Aexp`] and [`bexp::Bexp`] enums, which define
//! tree-like structures that explicitly model these expressions.
//!
//! # Commands
//! In the IMP grammar, a _command_ corresponds to a node in a program's abstract
//! syntax tree. These nodes are modelled by the [`cmd::Cmd`] enum, and in turn
//! they can be converted into [`Ast`]s to provide an opaque interface.

use nom::Finish;
use thiserror::Error;

use crate::lexer::{token::TokensRef, var::Var};

use self::cmd::{cmd, Cmd};

pub mod aexp;
pub mod bexp;
pub mod cmd;
pub mod tree;
mod util;

/// The error type thrown when trying to parse an [`Ast`] from [`Tokens`](crate::lexer::token::Tokens).
#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub struct AstParseError<'buf, 'src, T> {
    /// The position in the input where this error ocurred.
    pub location: TokensRef<'buf, 'src, T>,
}

/// An abstract syntax tree for an IMP program.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ast<V = Var<'static>, T = usize> {
    /// The root of this tree.
    root: Cmd<V, T>,
}

impl<'buf, 'src, T: Clone + Eq> TryFrom<TokensRef<'buf, 'src, T>> for Ast<Var<'src>, T> {
    type Error = AstParseError<'buf, 'src, T>;

    fn try_from(value: TokensRef<'buf, 'src, T>) -> Result<Self, Self::Error> {
        let (tail, root) = cmd(value).finish().map_err(|err| AstParseError {
            location: err.input,
        })?;
        debug_assert!(tail.is_empty());
        Ok(Self { root })
    }
}

impl<V, T> Ast<V, T> {
    /// Consumes `self` and applies the given function `f` to its `root`.
    pub fn map<F, U>(self, f: F) -> U
    where
        F: FnOnce(Cmd<V, T>) -> U,
    {
        f(self.root)
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn test_ast_map_impl() {
        let tokens: Tokens = "X := 1; Y := 2; Z := 3".try_into().unwrap();
        let ast: Ast = tokens.as_ref().try_into().unwrap();
        dbg!(ast.clone());

        fn count(node: Cmd<Var<'_>>) -> usize {
            // recursive definition:
            // the number of nodes in a tree is 1 + the number of nodes in all subtrees
            1 + match node {
                Cmd::Seq(left, right) => count(*left) + count(*right),
                Cmd::While(_, inner) => 1 + count(*inner),
                Cmd::If {
                    cond: _,
                    true_case,
                    false_case,
                } => 1 + count(*true_case) + count(*false_case),
                Cmd::Assign(_, _) => 2,
                Cmd::Skip => 0,
            }
        }

        assert_eq!(ast.map(count), 11);
    }
}
