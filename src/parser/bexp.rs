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

use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::fail,
    sequence::{delimited, preceded},
    IResult, Parser,
};

use crate::lexer::token::{Token, TokensRef};

use super::{
    aexp::{aexp, Aexp},
    util::{binary_expr, unbox2},
};

/// A boolean expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Bexp<'src, T = usize> {
    /// A boolean value.
    Atom(bool),
    /// The equality comparison, corresponding to [`Token::Equals`].
    Eq(Aexp<'src, T>, Aexp<'src, T>),
    /// The inequality comparison, corresponding to the token sequence of [`Token::LeftAngleBracket`]
    /// followed by [`Token::RightAngleBracket`].
    NotEq(Aexp<'src, T>, Aexp<'src, T>),
    /// The less-than comparison, corresponding to a single [`Token::LeftAngleBracket`].
    LessThan(Aexp<'src, T>, Aexp<'src, T>),
    /// The greater-than comparison, corresponding to a single [`Token::RightAngleBracket`].
    GreaterThan(Aexp<'src, T>, Aexp<'src, T>),
    /// The unary logical NOT operator, corresponding to [`Token::Not`].
    Not(Box<Self>),
    /// The binary logical AND operator, corresponding to [`Token::And`].
    And(Box<Self>, Box<Self>),
    /// The binary logical OR operator, corresponding to [`Token::Or`].
    Or(Box<Self>, Box<Self>),
}

impl<'src, T: std::fmt::Display> std::fmt::Display for Bexp<'src, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Atom(atom) => format!("{atom}"),
                Self::Eq(lhs, rhs) => format!("(= {lhs} {rhs})"),
                Self::NotEq(lhs, rhs) => format!("(!= {lhs} {rhs})"),
                Self::LessThan(lhs, rhs) => format!("(< {lhs} {rhs})"),
                Self::GreaterThan(lhs, rhs) => format!("(> {lhs} {rhs})"),
                Self::Not(inner) => format!("(not {inner})"),
                Self::And(lhs, rhs) => format!("(and {lhs} {rhs})"),
                Self::Or(lhs, rhs) => format!("(or {lhs} {rhs})"),
            }
        )
    }
}

/// The return type of parsers in the [`crate::parser::bexp`] module.
type BexpResult<'buf, 'src, T = usize> = IResult<TokensRef<'buf, 'src, T>, Bexp<'src, T>>;

/// Parses a [`Bexp`] from `input`.
pub fn bexp<'buf, 'src, T: Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    alt((connective, not, proposition)).parse(input)
}

/// Parses a [`Bexp::Atom`] from `input`.
fn atom<'buf, 'src, T: Clone>(input: TokensRef<'buf, 'src, T>) -> BexpResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::True, tail)) => Ok((tail.into(), Bexp::Atom(true))),
        Some((Token::False, tail)) => Ok((tail.into(), Bexp::Atom(false))),
        _ => fail(input),
    }
}

/// Parses a logical connective (either [`Bexp::And`] or [`Bexp::Or`]) from `input`.
fn connective<'buf, 'src, T: Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    delimited(
        tag(Token::LeftParen),
        alt((
            binary_expr(bexp, Token::Or, bexp, unbox2(Bexp::Or)),
            binary_expr(bexp, Token::And, bexp, unbox2(Bexp::And)),
        )),
        tag(Token::RightParen),
    )
    .parse(input)
}

fn not<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> BexpResult<'buf, 'src, T> {
    preceded(tag(Token::Not), bexp)
        .parse(input)
        .map(|(tail, expr)| (tail, Bexp::Not(Box::new(expr))))
}

/// Parses a proposition (i.e. nonrecursive variant of [`Bexp`]) from `input`.
fn proposition<'buf, 'src, T: Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> BexpResult<'buf, 'src, T> {
    let not_eq_tokens = TokensRef::new(&[Token::LeftAngleBracket, Token::RightAngleBracket]);

    alt((
        binary_expr(aexp, not_eq_tokens, aexp, Bexp::NotEq),
        binary_expr(aexp, Token::RightAngleBracket, aexp, Bexp::GreaterThan),
        binary_expr(aexp, Token::LeftAngleBracket, aexp, Bexp::LessThan),
        binary_expr(aexp, Token::Equals, aexp, Bexp::Eq),
        atom,
    ))
    .parse(input)
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn check_atom_parser() {
        let tokens = Tokens::<'_, usize>::try_from("not (true or (false and false))").unwrap();
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
        let tokens = Tokens::<'_, usize>::try_from("13 <> 12").unwrap();
        let (tail, prop) = proposition(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), prop.clone());

        assert!(tail.is_empty());
        assert_eq!(prop, Bexp::NotEq(Aexp::Int(13), Aexp::Int(12)));

        let tokens = Tokens::<'_, usize>::try_from("X = Y - 1").unwrap();
        let (tail, prop) = proposition(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), prop.clone());

        assert!(tail.is_empty());
        assert_eq!(
            prop,
            Bexp::Eq(
                Aexp::Var("X".into()),
                Aexp::Sub(Box::new(Aexp::Var("Y".into())), Box::new(Aexp::Int(1)))
            )
        );
    }

    #[test]
    fn check_bexp_parser() {
        let tokens = Tokens::<'_, usize>::try_from("not (X = 1 and Y > Z)").unwrap();
        let (tail, expr) = bexp(tokens.as_ref()).unwrap();
        eprintln!("parsed expr: {}", expr.clone());

        // all tokens should have been consumed
        assert!(tail.is_empty());

        // the expression should be (not (or (= X 1) (> Y Z)))
        assert_eq!(
            expr,
            Bexp::Not(Box::new(Bexp::Or(
                Box::new(Bexp::Eq(Aexp::Var("X".into()), Aexp::Int(1))),
                Box::new(Bexp::GreaterThan(
                    Aexp::Var("Y".into()),
                    Aexp::Var("Z".into())
                ))
            )))
        );
    }
}
