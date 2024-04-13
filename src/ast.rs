//! Abstract syntax trees and associated transformations.

use std::{collections::HashSet, hash::Hash};

use nom::Finish;

use crate::{
    int::ImpSize,
    lexer::token::TokensRef,
    parser::{
        cmd::{cmd, Cmd},
        expr::Expr,
    },
};

use self::tree::Tree;

pub mod tree;

/// An abstract syntax tree for an IMP program.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Ast<V, T = ImpSize> {
    /// The root of this tree.
    root: Cmd<V, T>,
}

impl<'buf, 'src, T: Clone + Eq> TryFrom<TokensRef<'buf, &'src str, T>> for Ast<&'src str, T> {
    type Error = nom::error::Error<TokensRef<'buf, &'src str, T>>;

    fn try_from(value: TokensRef<'buf, &'src str, T>) -> Result<Self, Self::Error> {
        let (tail, root) = cmd(value).finish()?;
        debug_assert!(tail.is_empty());
        Ok(Self { root })
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
    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn test_ast_map_impl() {
        let tokens: Tokens<_, usize> = "X := 1; Y := 2; Z := 3".try_into().unwrap();
        let ast: Ast<_, usize> = tokens.as_ref().try_into().unwrap();
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
