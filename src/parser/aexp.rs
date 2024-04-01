//! Arithmetic expressions.

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

/// An arithmetic expression.
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

type AexpResult<'buf, 'src, T = usize> = IResult<TokensRef<'buf, 'src, T>, Aexp<'src, T>>;

/// Parses a complete [`Aexp`] from `input`.
pub fn aexp<'buf, 'src, T: Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> AexpResult<'buf, 'src, T> {
    todo!()
}

/// Parses a high-precedence term, i.e. either an [`atom`] or an [`Aexp::Mul`].
fn factor<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    alt((atom, binary_expr(Token::Star, Aexp::Mul))).parse(input)
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
fn parens<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    delimited(tag(Token::LeftParen), aexp, tag(Token::RightParen)).parse(input)
}

/// Parses an atom from `input`, where an atom is considered to be one of
/// - an [`Aexp::Int`];
/// - an [`Aexp::Var`];
/// - a parenthesised expression.
fn atom<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T> {
    alt((int, var, parens)).parse(input)
}

const fn binary_expr<'buf, 'src, T: Clone + Eq>(
    operator: Token<'static, T>,
    constructor: fn(Box<Aexp<'src, T>>, Box<Aexp<'src, T>>) -> Aexp<'src, T>,
) -> impl FnMut(TokensRef<'buf, 'src, T>) -> AexpResult<'buf, 'src, T>
where
    'src: 'buf,
{
    move |input| {
        // this clone would be unnecessary if Token was Copy
        separated_pair(aexp, tag(operator.clone()), aexp)
            .parse(input)
            .map(|(tail, (lhs, rhs))| (tail, constructor(Box::new(lhs), Box::new(rhs))))
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use nom::bytes::complete::take;

    use crate::lexer::{self, token::Tokens};

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
}
