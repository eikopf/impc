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
//!       factor '-' factor
//!     | factor '+' factor
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

use nom::{
    branch::alt, bytes::complete::tag, combinator::fail, sequence::delimited, IResult, InputTake,
    Parser,
};

use crate::lexer::{
    token::{Token, TokensRef},
    var::Var,
};

use super::{
    tree::Tree,
    util::{binary_expr, unbox2},
};

/// An arithmetic expression, consisting of
/// - variables ([`Var`]s);
/// - integers (`T`s);
/// - multiplication expressions;
/// - addition expressions;
/// - subtraction expressions.
///
/// The [`Display`](std::fmt::Display) implementation
/// on this type produces an appropriate lisp-style
/// s-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Aexp<V, T = usize> {
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

impl<V, T> Aexp<V, T> {
    /// Constructs an [`Aexp::Var`] by cloning `var`.
    pub fn var_from<'src>(var: &'src str) -> Self
    where
        V: From<&'src str>,
    {
        Self::Var(var.into())
    }
}

/// The return type of parsers in the [`crate::parser::aexp`] module.
pub type AexpResult<'buf, 'src, T = usize> = IResult<TokensRef<'buf, 'src, T>, Aexp<Var<'src>, T>>;

/// Parses a complete [`Aexp`] from `input`.
pub fn aexp<'buf, 'src, T: 'buf + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((
        binary_expr(factor, Token::Minus, factor, unbox2(Aexp::Sub)),
        binary_expr(factor, Token::Plus, factor, unbox2(Aexp::Add)),
        factor,
    ))
    .parse(input)
}

/// Parses a high-precedence term, i.e. either a [`term`] or an [`Aexp::Mul`].
fn factor<'buf, 'src, T: 'buf + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((
        binary_expr(term, Token::Star, term, unbox2(Aexp::Mul)),
        term,
    ))
    .parse(input)
}

/// Parses a term from `input`, where a term is considered to be one of
/// - an [`Aexp::Int`];
/// - an [`Aexp::Var`];
/// - a parenthesised expression.
fn term<'buf, 'src, T: 'buf + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((int, var, parens)).parse(input)
}

/// Parses an [`Aexp::Int`] from `input`.
fn int<'buf, 'src, T: Clone>(input: TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    let (tail, head) = input.take_split(1);
    debug_assert!(head.len() == 1);

    match head.first() {
        Some(Token::Int(int)) => Ok((tail, Aexp::Int(int.clone()))),
        _ => fail(input),
    }
}

/// Parses an [`Aexp::Var`] from `input`.
fn var<'buf, 'src, T: Clone>(input: TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    let (tail, head) = input.take_split(1);
    debug_assert!(head.len() == 1);

    match head.first() {
        Some(Token::Var(var)) => Ok((tail, Aexp::Var(var.clone()))),
        _ => fail(input),
    }
}

/// Parses a parenthesised [`Aexp`], with no explicit precedence handling.
fn parens<'buf, 'src, T: 'buf + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    delimited(tag(Token::LeftParen), aexp, tag(Token::RightParen)).parse(input)
}

#[cfg(test)]
mod tests {
    use nom::sequence::separated_pair;

    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn check_int_parser() {
        let tokens = Tokens::try_from("149 * X").unwrap();
        let (tail, x) = int(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), x.clone());

        assert_eq!(x, Aexp::Int(149usize));
        assert_eq!(
            tail,
            TokensRef::new(&vec![Token::Star, Token::Var(Var::from("X"))])
        );

        let tokens = Tokens::<'_, usize>::try_from("X * 12").unwrap();
        let err = int(tokens.as_ref()).expect_err("expr begins with a variable");
        dbg!(err);
    }

    #[test]
    fn check_var_parser() {
        let tokens = Tokens::<'_, usize>::try_from("X * Y").unwrap();
        let (tail, res) = var(TokensRef::new(&tokens)).unwrap();
        dbg!(tail.clone(), res.clone());

        assert_eq!(res, Aexp::var_from("X"));
        assert_eq!(
            tail,
            TokensRef::new(&vec![Token::Star, Token::Var(Var::from("Y"))])
        );

        let (tail, (lhs, rhs)) = separated_pair(var, tag(Token::Star), var)
            .parse(TokensRef::new(&tokens))
            .unwrap();
        dbg!(lhs.clone(), rhs.clone());

        assert!(tail.is_empty());
        assert_eq!(lhs, Aexp::var_from("X"));
        assert_eq!(rhs, Aexp::var_from("Y"));
    }

    #[test]
    fn check_aexp_parser() {
        // in this first case, we expect to get (* (+ X 13) 6)
        let tokens = Tokens::<'_, usize>::try_from("(X+13)*6").unwrap();
        let (tail, expr) = aexp(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), expr.clone());

        assert!(tail.is_empty());
        assert_eq!(
            expr,
            Aexp::Mul(
                Box::new(Aexp::Add(
                    Box::new(Aexp::var_from("X")),
                    Box::new(Aexp::Int(13))
                )),
                Box::new(Aexp::Int(6))
            )
        );

        // in this second case with parentheses omitted, we expect to get (+ X (* 13 6))
        let tokens = Tokens::<'_, usize>::try_from("X+13*6").unwrap();
        let (tail, expr) = aexp(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), expr.clone());

        assert!(tail.is_empty());
        assert_eq!(
            expr,
            Aexp::Add(
                Box::new(Aexp::var_from("X")),
                Box::new(Aexp::Mul(Box::new(Aexp::Int(13)), Box::new(Aexp::Int(6)))),
            )
        );

        // in this third case, we expect to get exactly the same result as in the second case
        let tokens = Tokens::<'_, usize>::try_from("X+(13*6)").unwrap();
        let (tail, expr) = aexp(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), expr.clone());

        assert!(tail.is_empty());
        assert_eq!(
            expr,
            Aexp::Add(
                Box::new(Aexp::var_from("X")),
                Box::new(Aexp::Mul(Box::new(Aexp::Int(13)), Box::new(Aexp::Int(6)))),
            )
        );
    }
}
