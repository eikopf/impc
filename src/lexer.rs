//! A simple zero-copy lexer for IMP programs.

use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::take_while1,
    character::{
        complete::{digit1, multispace0},
        is_alphanumeric,
    },
    combinator::{all_consuming, map_res, verify},
    error::VerboseError,
    multi::many0,
    sequence::delimited,
    Finish, IResult, Parser,
};

use token::Token;

use self::token::TokenRef;

pub mod symbol;
pub mod token;

/// The general error type produced by [`crate::lexer`] parsers.
pub type LexError<E> = VerboseError<E>;
/// The general return type for [`crate::lexer`] parsers.
pub type LexResult<'src, T> = IResult<&'src str, TokenRef<'src, T>, LexError<&'src str>>;

/// Converts a `LexError<&str>` into a `LexError<String>` using [`String::from`].
pub fn owned_lex_error(error: LexError<&str>) -> LexError<String> {
    VerboseError {
        errors: error
            .errors
            .into_iter()
            .map(|(s, kind)| (String::from(s), kind))
            .collect(),
    }
}

/// Attempts to parse the entirety of `input` into a `Vec<Token<'_, T>>`,
/// either returning it completely or producing a [`VerboseError`].
pub fn parse_tokens<T: FromStr>(input: &str) -> Result<Vec<TokenRef<'_, T>>, VerboseError<&str>> {
    all_consuming(many0(delimited(
        multispace0,
        alt((symbol::glyph, symbol::keyword, int, var)),
        multispace0,
    )))
    .parse(input)
    .finish()
    .map(|(_tail, vec)| {
        debug_assert!(_tail.is_empty());
        vec
    })
    .map_err(|err| VerboseError { errors: err.errors })
}

/// Parses a [`Token::Var`] from `input`.
pub fn var<T>(input: &str) -> LexResult<'_, T> {
    verify(
        take_while1(|c: char| is_alphanumeric(c as u8) || c == '_'),
        |s: &str| !s.starts_with('_'),
    )
    .parse(input)
    .map(|(tail, name)| (tail, Token::Var(name)))
}

/// Parses a [`Token::Int`] from `input`.
pub fn int<T: FromStr>(input: &str) -> LexResult<'_, T> {
    map_res(digit1, T::from_str)
        .parse(input)
        .map(|(tail, value)| (tail, Token::Int(value)))
}

#[cfg(test)]
mod tests {
    use nom::error::convert_error;

    use super::*;

    #[test]
    fn var_parser_is_correct() {
        assert!(var::<usize>("Var_name trailing")
            .is_ok_and(|res| res == (" trailing", Token::Var(&"Var_name"))));

        assert!(var::<usize>("_illegal_name").is_err());

        assert!(var::<usize>("X").is_ok());
        assert!(var::<usize>("X := ").is_ok());
        assert!(var::<usize>("X := 13").is_ok());
        assert!(var::<usize>("X := 13;").is_ok());
    }

    #[test]
    fn check_small_example_program() {
        let source = r#"
        X := 706;
        Y := 0;
        Z := 13;
        while Z <> Y do
            Y := Y + 1;
            X := X * 2;
        od
        "#;

        dbg!(source);

        let tokens = match parse_tokens::<usize>(source) {
            Ok(tokens) => tokens,
            Err(error) => {
                let nice_error = convert_error(source, error);
                println!("{}", nice_error);

                assert!(false);
                unreachable!()
            }
        };

        dbg!(tokens);
        // we assume that if parsing succeeded, this test passed.
    }
}
