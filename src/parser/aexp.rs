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
//! ```bnf
//! aexp ::=
//!       factor '+' factor
//!     | factor '-' factor
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
    branch::alt,
    bytes::complete::tag,
    combinator::fail,
    sequence::{delimited, separated_pair},
    IResult, InputTake, Parser,
};

use crate::lexer::{
    token::{Token, TokensRef},
    var::Var,
};

/// An arithmetic expression, consisting of
/// - variables ([`Var`]s);
/// - integers (`T`s);
/// - multiplication expressions;
/// - addition expressions;
/// - subtraction expressions.
///
/// The [`Display`](std::fmt::Display) implementation
/// on this type produces the appropriate lisp-style
/// s-expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Aexp<'src, T = usize> {
    /// An integer.
    Int(T),
    /// A variable name.
    Var(Var<'src>),
    /// Binary addition.
    Add(Box<Self>, Box<Self>),
    /// Binary multiplication.
    Mul(Box<Self>, Box<Self>),
    /// Binary left-to-right subtraction.
    Sub(Box<Self>, Box<Self>),
}

impl<'src, T: std::fmt::Display> std::fmt::Display for Aexp<'src, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Aexp::Int(int) => int.to_string(),
                Aexp::Var(var) => var.get().to_string(),
                Aexp::Add(lhs, rhs) => format!("(+ {lhs} {rhs})"),
                Aexp::Mul(lhs, rhs) => format!("(* {lhs} {rhs})"),
                Aexp::Sub(lhs, rhs) => format!("(- {lhs} {rhs})"),
            }
        )
    }
}

/// The return type of parsers in the [`crate::parser::aexp`] module.
type AexpResult<'buf, 'src, T = usize> = IResult<TokensRef<'buf, 'src, T>, Aexp<'src, T>>;

/// Parses a complete [`Aexp`] from `input`.
pub fn aexp<'buf, 'src, T: 'src + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((
        binary_expr(factor, Token::Plus, factor, Aexp::Add),
        binary_expr(factor, Token::Minus, factor, Aexp::Sub),
        factor,
    ))
    .parse(input)
}

/// Parses a high-precedence term, i.e. either a [`term`] or an [`Aexp::Mul`].
fn factor<'buf, 'src, T: 'src + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    alt((binary_expr(term, Token::Star, term, Aexp::Mul), term)).parse(input)
}

/// Parses a term from `input`, where a term is considered to be one of
/// - an [`Aexp::Int`];
/// - an [`Aexp::Var`];
/// - a parenthesised expression.
fn term<'buf, 'src, T: 'src + Clone + Eq>(
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
fn parens<'buf, 'src, T: 'src + Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    delimited(tag(Token::LeftParen), aexp, tag(Token::RightParen)).parse(input)
}

/// The type of a function that constructs new [`Aexp`] from subexpressions.
type AexpCons<'src, T = usize> = fn(Box<Aexp<'src, T>>, Box<Aexp<'src, T>>) -> Aexp<'src, T>;

/// A parser matching the sequence `(lhs, operator, rhs)`, which
/// uses the given `constructor` to produce a new [`Aexp`] in the
/// success case.
const fn binary_expr<'buf, 'src: 'buf, T: 'src + Clone + Eq>(
    lhs: impl FnMut(TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> + Copy,
    operator: Token<'src, T>,
    rhs: impl FnMut(TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> + Copy,
    constructor: AexpCons<'src, T>,
) -> impl FnMut(TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    move |input| {
        // this clone would be unnecessary if Token was Copy
        separated_pair(lhs, tag(operator.clone()), rhs)
            .parse(input)
            .map(|(tail, (lhs, rhs))| (tail, constructor(Box::new(lhs), Box::new(rhs))))
    }
}

#[cfg(test)]
mod tests {
    use nom::bytes::complete::take;

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
            TokensRef::new(&vec![
                Token::Whitespace,
                Token::Star,
                Token::Whitespace,
                Token::Var(Var::from("X"))
            ])
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

        assert_eq!(res, Aexp::Var(Var::from("X")));
        assert_eq!(
            tail,
            TokensRef::new(&vec![
                Token::Whitespace,
                Token::Star,
                Token::Whitespace,
                Token::Var(Var::from("Y"))
            ])
        );

        let (tail, (lhs, rhs)) = separated_pair(var, take(3usize), var)
            .parse(TokensRef::new(&tokens))
            .unwrap();
        dbg!(lhs.clone(), rhs.clone());

        assert!(tail.is_empty());
        assert_eq!(lhs, Aexp::Var(Var::from("X")));
        assert_eq!(rhs, Aexp::Var(Var::from("Y")));
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
                    Box::new(Aexp::Var("X".into())),
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
                Box::new(Aexp::Var("X".into())),
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
                Box::new(Aexp::Var("X".into())),
                Box::new(Aexp::Mul(Box::new(Aexp::Int(13)), Box::new(Aexp::Int(6)))),
            )
        );
    }
}
