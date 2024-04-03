//! Simple lexer for `.imp` files.

use std::str::FromStr;

use nom::{
    branch::alt, character::complete::multispace0, combinator::all_consuming, error::VerboseError, multi::many0, sequence::delimited, Finish, IResult, Parser
};

use token::Token;

pub mod int;
pub mod symbol;
pub mod token;
pub mod var;

/// The general return type for [`crate::lexer`] parsers.
pub type LexResult<'src, T> = IResult<&'src str, Token<'src, T>, VerboseError<&'src str>>;

/// Attempts to parse the entirety of `input` into a `Vec<Token<'_, T>>`,
/// either returning it completely or producing a [`VerboseError`].
pub fn parse_tokens<T: FromStr>(input: &str) -> Result<Vec<Token<'_, T>>, VerboseError<&str>> {
    all_consuming(many0(delimited(
        multispace0,
        alt((symbol::glyph, symbol::keyword, int::int, var::var)),
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

#[cfg(test)]
mod tests {
    use nom::error::convert_error;

    use super::*;

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
