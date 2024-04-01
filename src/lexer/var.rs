//! IMP variables and variable parsing.

use byteyarn::{YarnBox, YarnRef};
use nom::{bytes::complete::take_while1, character::is_alphanumeric, combinator::verify, Parser};

use super::{LexResult, token::Token};

/// A valid IMP variable, guaranteed to begin
/// with a latin character and to have a body
/// composed of latin characters, arabic numerals,
/// and underscores.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Var<'src>(YarnBox<'src, str>);

impl<'src> From<&'src str> for Var<'src> {
    fn from(value: &'src str) -> Self {
        Self(YarnBox::from(value))
    }
}

impl<'src> Var<'src> {
    /// Returns a reference to the underlying [`YarnBox`].
    pub fn get(&self) -> YarnRef<'_, str> {
        self.0.as_ref()
    }
}

/// Parses a [`Token::Var`] from `input`.
pub fn var<T>(input: &str) -> LexResult<'_, T> {
    verify(
        take_while1(|c: char| is_alphanumeric(c as u8) || c == '_'),
        |s: &str| !s.starts_with('_'),
    )
    .parse(input)
    .map(|(tail, name)| (tail, Token::Var(Var(YarnBox::from(name)))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn var_parser_is_correct() {
        assert!(var::<usize>("Var_name trailing")
            .is_ok_and(|res| res == (" trailing", Token::Var(Var(YarnBox::from("Var_name"))))));

        assert!(var::<usize>("_illegal_name").is_err());

        assert!(var::<usize>("X").is_ok());
        assert!(var::<usize>("X := ").is_ok());
        assert!(var::<usize>("X := 13").is_ok());
        assert!(var::<usize>("X := 13;").is_ok());
    }
}
