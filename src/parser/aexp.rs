//! Arithmetic expressions.
//!
//! # Grammar
//! The grammar for arithmetic expressions in IMP was
//! originally defined in an ANTLR4 `.g4` file (see below),
//! and would result in unbounded left-recursion if it was
//! simply translated directly into a [`nom`] parser.
//!
//! ```antlr
//! aexp : INT                          #Atom
//!      | VAR                          #Variable
//!      | '(' inner=aexp ')'           #Brackets
//!      | left=aexp '*' right=aexp     #Mult
//!      | left=aexp '+' right=aexp     #Add
//!      | left=aexp '-' right=aexp     #Sub
//!      ;
//! ```
//!
//! To resolve this, the grammar was refactored into an
//! unambiguous EBNF form (see below); this also avoids
//! alternative parsing methods (like e.g. Pratt parsing)
//! which mandate additional precedence-related bookkeeping.
//!
//! ```raw
//! aexp ::=
//!       factor '-' aexp
//!     | factor '+' aexp
//!     | factor
//!
//! factor ::=
//!       term '*' term
//!     | term
//!
//! term ::=
//!       INT
//!     | VAR
//!     | '(' aexp ')'
//! ```

use std::{
    collections::HashSet,
    hash::Hash,
    ops::{Add, Mul, Sub},
};

use nom::{branch::alt, combinator::fail, sequence::delimited, IResult, Parser};
use num_traits::Unsigned;

use crate::{
    tree::{NodeCount, Tree},
    int::ImpSize,
    lexer::token::Token,
};

use super::{
    expr::Expr,
    util::{binary_expr, token},
    ParserInput,
};

/// An arithmetic expression.
///
/// Arithmetic expressions consist of
/// - variables (`V`s);
/// - integers (`T`s);
/// - multiplication expressions;
/// - addition expressions;
/// - subtraction expressions.
///
/// The [`Display`](std::fmt::Display) implementation
/// on this type produces an appropriate lisp-style
/// s-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Aexp<V, T = ImpSize> {
    /// An integer.
    Int(T),
    /// A variable name.
    Var(V),
    /// Binary addition.
    Add(Box<Self>, Box<Self>),
    /// Binary multiplication.
    Mul(Box<Self>, Box<Self>),
    /// Binary left-to-right subtraction.
    Sub(Box<Self>, Box<Self>),
}

impl<V, T> Add for Aexp<V, T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Aexp::Add(Box::new(self), Box::new(rhs))
    }
}

impl<V, T> Mul for Aexp<V, T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Aexp::Mul(Box::new(self), Box::new(rhs))
    }
}

impl<V, T> Sub for Aexp<V, T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Aexp::Sub(Box::new(self), Box::new(rhs))
    }
}

impl<V: std::fmt::Display, T: std::fmt::Display> std::fmt::Display for Aexp<V, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Aexp::Int(int) => format!("{int}"),
                Aexp::Var(var) => format!("{var}"),
                Aexp::Add(lhs, rhs) => format!("(+ {lhs} {rhs})"),
                Aexp::Mul(lhs, rhs) => format!("(* {lhs} {rhs})"),
                Aexp::Sub(lhs, rhs) => format!("(- {lhs} {rhs})"),
            }
        )
    }
}

impl<V, T: num_traits::ConstZero> num_traits::ConstZero for Aexp<V, T> {
    const ZERO: Self = Aexp::Int(T::ZERO);
}

impl<V, T: num_traits::ConstOne> num_traits::ConstOne for Aexp<V, T> {
    const ONE: Self = Aexp::Int(T::ONE);
}

impl<V, T: num_traits::Zero> num_traits::Zero for Aexp<V, T> {
    #[inline(always)]
    fn zero() -> Self {
        Aexp::Int(T::zero())
    }

    fn is_zero(&self) -> bool {
        matches!(self, Aexp::Int(int) if int.is_zero())
    }
}

impl<V, T: num_traits::One> num_traits::One for Aexp<V, T> {
    fn one() -> Self {
        Aexp::Int(T::one())
    }
}

impl<V, T> Tree for Aexp<V, T> {
    type Node = Self;

    #[inline(always)]
    fn root(self) -> Self::Node {
        self
    }

    #[inline(always)]
    fn map<U, F>(self, op: F) -> U
    where
        F: FnOnce(Self::Node) -> U,
    {
        op(self)
    }
}

impl<V, T, U> NodeCount<U> for Aexp<V, T>
where
    U: Unsigned,
{
    fn count_nodes(&self) -> U {
        // recursive definition: the number of nodes in a tree is 1 + the number of nodes in its
        // subtrees
        U::one()
            + match self {
                Self::Add(lhs, rhs) | Self::Mul(lhs, rhs) | Self::Sub(lhs, rhs) => {
                    // explicit call required to help type inference at deref coercion boundary
                    <Aexp<V, T> as NodeCount<U>>::count_nodes(lhs) + rhs.count_nodes()
                }
                Self::Int(_) | Self::Var(_) => U::zero(),
            }
    }
}

impl<V, T> Expr for Aexp<V, T>
where
    V: Eq + Hash,
{
    type Name = V;

    fn names(&self) -> HashSet<&Self::Name> {
        match self {
            Aexp::Int(_) => HashSet::new(),
            Aexp::Var(var) => HashSet::from([var]),
            Aexp::Add(lhs, rhs) | Aexp::Mul(lhs, rhs) | Aexp::Sub(lhs, rhs) => {
                HashSet::union(&lhs.names(), &rhs.names())
                    .map(Clone::clone)
                    .collect()
            }
        }
    }
}

impl<V, T> Aexp<V, T> {
    /// Constructs an [`Aexp::Var`] by invoking [`From::from`].
    pub fn var_from<U>(var: U) -> Self
    where
        V: From<U>,
    {
        Self::Var(var.into())
    }
}

/// The return type of parsers in the [`crate::parser::aexp`] module.
pub type AexpResult<'buf, 'src, T = usize> =
    IResult<ParserInput<'buf, 'src, T>, Aexp<&'src str, T>>;

/// Parses a complete [`Aexp`] from `input`.
pub fn aexp<'buf, 'src, T: 'buf + Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((
        binary_expr(factor, token(&Token::Minus), aexp, Aexp::sub),
        binary_expr(factor, token(&Token::Plus), aexp, Aexp::add),
        factor,
    ))
    .parse(input)
}

/// Parses a high-precedence term, i.e. either a [`term`] or an [`Aexp::Mul`].
fn factor<'buf, 'src, T: 'buf + Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((
        binary_expr(term, token(&Token::Star), term, Aexp::mul),
        term,
    ))
    .parse(input)
}

/// Parses a term from `input`, where a term is considered to be one of
/// - an [`Aexp::Int`];
/// - an [`Aexp::Var`];
/// - a parenthesised expression.
fn term<'buf, 'src, T: 'buf + Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((int, var, parens)).parse(input)
}

/// Parses an [`Aexp::Int`] from `input`.
fn int<'buf, 'src, T: Clone>(input: ParserInput<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::Int(int), tail)) => Ok((tail, Aexp::Int(int.clone()))),
        _ => fail(input),
    }
}

/// Parses an [`Aexp::Var`] from `input`.
fn var<'buf, 'src, T>(input: ParserInput<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::Var(var), tail)) => Ok((tail, Aexp::Var(var))),
        _ => fail(input),
    }
}

/// Parses a parenthesised [`Aexp`], with no explicit precedence handling.
fn parens<'buf, 'src, T: 'buf + Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    delimited(token(&Token::LeftParen), aexp, token(&Token::RightParen)).parse(input)
}

#[cfg(test)]
mod tests {
    use nom::sequence::separated_pair;

    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn check_int_parser() {
        let tokens = Tokens::try_from("149 * X").unwrap();
        let (tail, x) = int(tokens.as_slice()).unwrap();
        dbg!(tail, x.clone());

        assert_eq!(x, Aexp::Int(149usize));
        assert_eq!(tail, &vec![Token::Star, Token::Var("X")]);

        let tokens = Tokens::<_, usize>::try_from("X * 12").unwrap();
        let err = int(tokens.as_slice()).expect_err("expr begins with a variable");
        dbg!(err);
    }

    #[test]
    fn check_var_parser() {
        let tokens = Tokens::<_, usize>::try_from("X * Y").unwrap();
        let (tail, res) = var(tokens.as_slice()).unwrap();
        dbg!(tail, res.clone());

        assert_eq!(res, Aexp::var_from("X"));
        assert_eq!(tail, &vec![Token::Star, Token::Var("Y")]);

        let (tail, (lhs, rhs)) = separated_pair(var, token(&Token::Star), var)
            .parse(tokens.as_slice())
            .unwrap();
        dbg!(lhs.clone(), rhs.clone());

        assert!(tail.is_empty());
        assert_eq!(lhs, Aexp::var_from("X"));
        assert_eq!(rhs, Aexp::var_from("Y"));
    }

    #[test]
    fn check_aexp_parser() {
        // in this first case, we expect to get (* (+ X 13) 6)
        let tokens = Tokens::<_, usize>::try_from("(X+13)*6").unwrap();
        let (tail, expr) = aexp(tokens.as_slice()).unwrap();
        dbg!(tail, expr.clone());

        assert!(tail.is_empty());
        assert_eq!(expr, (Aexp::var_from("X") + Aexp::Int(13)) * Aexp::Int(6));

        // in this second case with parentheses omitted, we expect to get (+ X (* 13 6))
        let tokens = Tokens::<_, usize>::try_from("X+13*6").unwrap();
        let (tail, expr) = aexp(tokens.as_slice()).unwrap();
        dbg!(tail, expr.clone());

        assert!(tail.is_empty());
        assert_eq!(expr, Aexp::var_from("X") + (Aexp::Int(13) * Aexp::Int(6)));

        // in this third case, we expect to get exactly the same result as in the second case
        let tokens = Tokens::<_, usize>::try_from("X+(13*6)").unwrap();
        let (tail, expr) = aexp(tokens.as_slice()).unwrap();
        dbg!(tail, expr.clone());

        assert!(tail.is_empty());
        assert_eq!(expr, Aexp::var_from("X") + (Aexp::Int(13) * Aexp::Int(6)));
    }
}
