//! Boolean expressions.
//!
//! # Grammar
//! The grammar for boolean expressions in IMP was originally
//! given in an ANTLR4 `.g4` file (see below), where it includes
//! references to the presumed-defined [`aexp`](super::aexp) parser.
//!
//! ```antlr
//! bexp : 'true'                                     #True
//!      | 'false'                                    #False
//!      | left=aexp '=' right=aexp                   #Equal
//!      | left=aexp '<' right=aexp                   #Smaller
//!      | left=aexp '>' right=aexp                   #Greater
//!      | left=aexp '<>' right=aexp                  #Inequality
//!      | 'not' inner=bexp                           #Not
//!      | '(' left=bexp 'and' right=bexp ')'         #And
//!      | '(' left=bexp 'or' right=bexp ')'          #Or
//!      ;
//! ```
//!
//! This has a few strange characteristics; most notably IMP considers
//! parentheses to be valid in a boolean expression only if they appear
//! around `and` or `or`, and indeed mandates their usage with these
//! logical connectives (presumably this is to avoid precendence ambiguity).
//!
//! # Desugaring
//! To avoid code duplication, the inequality (`<>`) operator is desugared as `not <lhs> = <rhs>`.

use std::{
    collections::HashSet,
    hash::Hash,
    ops::{BitAnd, BitOr, Not},
};

use nom::{
    branch::alt,
    combinator::fail,
    sequence::{delimited, preceded},
    IResult, Parser,
};

use int::ImpSize;
use lexer::token::Token;
use tree::Tree;

use super::{
    aexp::{aexp, Aexp},
    expr::Expr,
    util::{binary_expr, token, tokens},
    ParserError, ParserInput,
};

/// A boolean expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Bexp<V, T = ImpSize> {
    /// A boolean value.
    Atom(bool),
    /// The equality comparison, corresponding to [`Token::Equals`].
    Eq(Aexp<V, T>, Aexp<V, T>),
    /// The less-than comparison, corresponding to a single [`Token::LeftAngleBracket`].
    LessThan(Aexp<V, T>, Aexp<V, T>),
    /// The greater-than comparison, corresponding to a single [`Token::RightAngleBracket`].
    GreaterThan(Aexp<V, T>, Aexp<V, T>),
    /// The unary logical NOT operator, corresponding to [`Token::Not`].
    Not(Box<Self>),
    /// The binary logical AND operator, corresponding to [`Token::And`].
    And(Box<Self>, Box<Self>),
    /// The binary logical OR operator, corresponding to [`Token::Or`].
    Or(Box<Self>, Box<Self>),
}

impl<V, T> Not for Bexp<V, T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Bexp::Not(Box::new(self))
    }
}

impl<V, T> BitAnd for Bexp<V, T> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Bexp::And(Box::new(self), Box::new(rhs))
    }
}

impl<V, T> BitOr for Bexp<V, T> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Bexp::Or(Box::new(self), Box::new(rhs))
    }
}

impl<V, T> std::fmt::Display for Bexp<V, T>
where
    V: std::fmt::Display,
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Atom(atom) => format!("{atom}"),
                Self::Eq(lhs, rhs) => format!("(= {lhs} {rhs})"),
                Self::LessThan(lhs, rhs) => format!("(< {lhs} {rhs})"),
                Self::GreaterThan(lhs, rhs) => format!("(> {lhs} {rhs})"),
                Self::Not(inner) => format!("(not {inner})"),
                Self::And(lhs, rhs) => format!("(and {lhs} {rhs})"),
                Self::Or(lhs, rhs) => format!("(or {lhs} {rhs})"),
            }
        )
    }
}

impl<V, T> Tree for Bexp<V, T> {
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

impl<V, T> Expr for Bexp<V, T>
where
    V: Eq + Hash,
{
    type Name = V;

    fn names(&self) -> HashSet<&Self::Name> {
        match self {
            Bexp::Atom(_) => HashSet::new(),
            Bexp::Eq(lhs, rhs) | Bexp::LessThan(lhs, rhs) | Bexp::GreaterThan(lhs, rhs) => {
                HashSet::union(&lhs.names(), &rhs.names())
                    .map(Clone::clone)
                    .collect()
            }
            Bexp::Not(inner) => inner.names(),
            Bexp::And(lhs, rhs) | Bexp::Or(lhs, rhs) => HashSet::union(&lhs.names(), &rhs.names())
                .map(Clone::clone)
                .collect(),
        }
    }
}

impl<V, T> Bexp<V, T> {
    /// The `true` atom.
    pub const TRUE: Self = Bexp::Atom(true);

    /// The `false` atom.
    pub const FALSE: Self = Bexp::Atom(false);

    /// Constructs a [`Bexp`] corresponding to `lhs = rhs`.
    pub fn eq(lhs: Aexp<V, T>, rhs: Aexp<V, T>) -> Self {
        Bexp::Eq(lhs, rhs)
    }

    /// Constructs a [`Bexp`] corresponding to `lhs < rhs`.
    pub fn lt(lhs: Aexp<V, T>, rhs: Aexp<V, T>) -> Self {
        Bexp::LessThan(lhs, rhs)
    }

    /// Constructs a [`Bexp`] corresponding to `lhs > rhs`.
    pub fn gt(lhs: Aexp<V, T>, rhs: Aexp<V, T>) -> Self {
        Bexp::GreaterThan(lhs, rhs)
    }

    /// Maps `op` over the variable nodes of `self`, leaving all other nodes unchanged.
    pub fn map_vars<F, U>(self, op: &F) -> Bexp<U, T>
    where
        F: Fn(V) -> U,
    {
        match self {
            Bexp::Atom(atom) => Bexp::Atom(atom),
            Bexp::Eq(lhs, rhs) => Bexp::eq(lhs.map_vars(op), rhs.map_vars(op)),
            Bexp::LessThan(lhs, rhs) => Bexp::lt(lhs.map_vars(op), rhs.map_vars(op)),
            Bexp::GreaterThan(lhs, rhs) => Bexp::gt(lhs.map_vars(op), rhs.map_vars(op)),
            Bexp::Not(inner) => !(inner.map_vars(op)),
            Bexp::And(lhs, rhs) => lhs.map_vars(op) & rhs.map_vars(op),
            Bexp::Or(lhs, rhs) => lhs.map_vars(op) | rhs.map_vars(op),
        }
    }
}

/// The return type of parsers in the [`crate::parser::bexp`] module.
pub type BexpResult<'buf, 'src, T = usize> =
    IResult<ParserInput<'buf, 'src, T>, Bexp<&'src str, T>, ParserError<'buf, 'src, T>>;

/// Parses a [`Bexp`] from `input`.
pub fn bexp<'buf, 'src, T: Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    alt((connective, not, proposition)).parse(input)
}

/// Parses a [`Bexp::Atom`] from `input`.
fn atom<'buf, 'src, T: Clone>(input: ParserInput<'buf, 'src, T>) -> BexpResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::True, tail)) => Ok((tail, Bexp::Atom(true))),
        Some((Token::False, tail)) => Ok((tail, Bexp::Atom(false))),
        _ => fail(input),
    }
}

/// Parses a logical connective (either [`Bexp::And`] or [`Bexp::Or`]) from `input`.
fn connective<'buf, 'src, T: Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    delimited(
        token(&Token::LeftParen),
        alt((
            binary_expr(bexp, token(&Token::Or), bexp, Bexp::bitor),
            binary_expr(bexp, token(&Token::And), bexp, Bexp::bitand),
        )),
        token(&Token::RightParen),
    )
    .parse(input)
}

/// Parses a [`Bexp::Not`] from `input`.
fn not<'buf, 'src, T: Clone + Eq>(input: ParserInput<'buf, 'src, T>) -> BexpResult<'buf, 'src, T> {
    preceded(token(&Token::Not), bexp)
        .parse(input)
        .map(|(tail, expr)| (tail, !expr))
}

/// Parses a proposition (i.e. nonrecursive variant of [`Bexp`]) from `input`.
fn proposition<'buf, 'src, T: Clone + Eq>(
    input: ParserInput<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    let not_eq_tokens = &[Token::LeftAngleBracket, Token::RightAngleBracket];

    alt((
        binary_expr(aexp, tokens(not_eq_tokens), aexp, |lhs, rhs| {
            !Bexp::eq(lhs, rhs)
        }),
        binary_expr(aexp, token(&Token::RightAngleBracket), aexp, Bexp::gt),
        binary_expr(aexp, token(&Token::LeftAngleBracket), aexp, Bexp::lt),
        binary_expr(aexp, token(&Token::Equals), aexp, Bexp::eq),
        atom,
    ))
    .parse(input)
}

#[cfg(test)]
mod tests {
    use lexer::token::Tokens;

    use super::*;

    #[test]
    fn check_atom_parser() {
        let tokens = Tokens::<_, usize>::try_from("not (true or (false and false))").unwrap();
        let parse_results = tokens
            .iter()
            .map(|token| atom(std::slice::from_ref(token).into()));
        dbg!(parse_results.clone().collect::<Vec<_>>());

        // check that the parse always consumes the token in the Ok case
        assert!(parse_results
            .clone()
            .filter(Result::is_ok)
            .all(|res| res.is_ok_and(|(tail, _)| tail.is_empty())));

        // the rest of this test is essentially just "hey, we didn't fail!".
    }

    #[test]
    fn check_proposition_parser() {
        let tokens = Tokens::<_, usize>::try_from("13 <> 12").unwrap();
        let (tail, prop) = proposition(tokens.as_slice()).unwrap();
        dbg!(tail, prop.clone());

        assert!(tail.is_empty());
        assert_eq!(prop, !Bexp::Eq(Aexp::Int(13), Aexp::Int(12)));

        let tokens = Tokens::<_, usize>::try_from("X = Y - 1").unwrap();
        let (tail, prop) = proposition(tokens.as_slice()).unwrap();
        dbg!(tail, prop.clone());

        assert!(tail.is_empty());
        assert_eq!(
            prop,
            Bexp::eq(Aexp::var_from("X"), Aexp::var_from("Y") - Aexp::Int(1))
        );
    }

    #[test]
    fn check_bexp_parser() {
        let tokens = Tokens::<_, usize>::try_from("not (X = 1 or Y > Z)").unwrap();
        let (tail, expr) = bexp(tokens.as_slice()).unwrap();
        eprintln!("parsed expr: {}", expr.clone());

        // all tokens should have been consumed
        assert!(tail.is_empty());

        // the expression should be (not (or (= X 1) (> Y Z)))
        assert_eq!(
            expr,
            !(Bexp::eq(Aexp::var_from("X"), Aexp::Int(1))
                | Bexp::gt(Aexp::var_from("Y"), Aexp::var_from("Z")))
        );
    }
}
