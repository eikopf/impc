//! Basic parsing functionality for IMP integers.

use std::str::FromStr;

use nom::{character::complete::digit1, combinator::map_res, Parser};

use super::{LexResult, token::Token};

/// Parses a [`Token::Int`] from `input`.
pub fn int<T: FromStr>(input: &str) -> LexResult<'_, T> {
    map_res(digit1, T::from_str)
        .parse(input)
        .map(|(tail, value)| (tail, Token::Int(value)))
}
