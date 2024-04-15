//! Abstract syntax trees and associated transformations.

use std::{collections::HashSet, hash::Hash, str::FromStr};

use nom::Finish;
use thiserror::Error;

use crate::{
    int::ImpSize,
    lexer::{owned_lex_error, token::Tokens},
    parser::{
        cmd::{cmd, Cmd},
        expr::Expr,
        owned_parser_error, ParserError, ParserInput,
    },
    tree::Tree,
};

/// The error type produced when failing to convert a [`String`]
/// into an [`Ast`] with the corresponding [`FromStr`] impl.
#[derive(Debug, Error, PartialEq)]
pub enum AstFromStringError<T> {
    /// The error produced if the conversion fails in the lexer.
    #[error("Error occurred in lexer: {0}")]
    Lexer(nom::error::VerboseError<String>),
    /// The error produced if the conversion fails in the parser.
    #[error("Error occurred in parser: {0}")]
    Parser(nom::error::Error<Tokens<String, T>>),
}

/// An abstract syntax tree for an IMP program.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ast<V, T = ImpSize> {
    /// The root of this tree.
    root: Cmd<V, T>,
}

impl<'buf, 'src, T> TryFrom<ParserInput<'buf, 'src, T>> for Ast<&'src str, T>
where
    'src: 'buf,
    T: Clone + Eq,
{
    type Error = ParserError<'buf, 'src, T>;

    fn try_from(value: ParserInput<'buf, 'src, T>) -> Result<Self, Self::Error> {
        let (tail, root) = cmd(value).finish()?;
        debug_assert!(tail.is_empty());
        Ok(Self { root })
    }
}

impl<'buf, 'src, T> FromStr for Ast<String, T>
where
    'src: 'buf,
    T: 'buf + Clone + Eq + FromStr,
{
    type Err = AstFromStringError<T>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens: Tokens<&str, T> = s
            .try_into()
            .map_err(|err| AstFromStringError::Lexer(owned_lex_error(err)))?;

        let root: Cmd<&str, T> = cmd(&tokens)
            .finish()
            .map(|(_tail, cmd)| cmd)
            .map_err(|err| AstFromStringError::Parser(owned_parser_error(err)))?;

        Ok(Ast {
            root: root.map_vars(&String::from),
        })
    }
}

impl<V, T> Tree for Ast<V, T> {
    type Node = Cmd<V, T>;

    #[inline(always)]
    fn root(self) -> Self::Node {
        self.root
    }

    #[inline(always)]
    fn map<U, F>(self, op: F) -> U
    where
        F: FnOnce(Self::Node) -> U,
    {
        op(self.root)
    }
}

impl<V, T> Ast<V, T> {
    /// Returns the variables mentioned in `self`.
    pub fn names(&self) -> HashSet<&V>
    where
        V: Eq + Hash,
    {
        self.root.names()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ast_map_impl() {
        let tokens: Tokens<_, usize> = "X := 1; Y := 2; Z := 3".try_into().unwrap();
        let ast: Ast<_, usize> = tokens.as_slice().try_into().unwrap();
        dbg!(ast.clone());
        dbg!(ast.clone().names());

        fn count(node: Cmd<&str, usize>) -> usize {
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
