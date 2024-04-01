//! Simple parsers for the basic symbols and keywords in an IMP program.

use nom::{
    branch::alt,
    character::complete::{char, multispace1},
    bytes::complete::tag,
    Parser,
};

use super::{LexResult, token::Token};

/// Parses a [`Token::Whitespace`] from `input`.
pub fn whitespace<T>(input: &str) -> LexResult<'_, T> {
    multispace1(input).map(|(tail, _)| (tail, Token::Whitespace))
}

/// Parses a non-keyword symbol from `input`.
pub fn glyph<T>(input: &str) -> LexResult<'_, T> {
    alt((
        semicolon,
        assign,
        equals,
        left_paren,
        right_paren,
        left_angle_bracket,
        right_angle_bracket,
        star,
        plus,
        minus,
    )).parse(input)
}

/// Parses a keyword symbol from `input`.
pub fn keyword<T>(input: &str) -> LexResult<'_, T> {
    alt((
        skip,
        r#if,
        then,
        r#else,
        fi,
        r#while,
        r#do,
        od,
        r#true,
        r#false,
        not,
        and,
        or,
    )).parse(input)
}

/// Parses a [`Token::Semicolon`] from `input`.
fn semicolon<T>(input: &str) -> LexResult<'_, T> {
    char(';')
        .parse(input)
        .map(|(tail, _)| (tail, Token::Semicolon))
}

/// Parses a [`Token::LeftParen`] from `input`.
fn left_paren<T>(input: &str) -> LexResult<'_, T> {
    char('(')
        .parse(input)
        .map(|(tail, _)| (tail, Token::LeftParen))
}

/// Parses a [`Token::RightParen`] from `input`.
fn right_paren<T>(input: &str) -> LexResult<'_, T> {
    char(')')
        .parse(input)
        .map(|(tail, _)| (tail, Token::RightParen))
}

/// Parses a [`Token::Assign`] from `input`.
fn assign<T>(input: &str) -> LexResult<'_, T> {
    tag(":=")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Assign))
}

/// Parses a [`Token::Star`] from `input`.
fn star<T>(input: &str) -> LexResult<'_, T> {
    char('*').parse(input).map(|(tail, _)| (tail, Token::Star))
}

/// Parses a [`Token::Plus`] from `input`.
fn plus<T>(input: &str) -> LexResult<'_, T> {
    char('+').parse(input).map(|(tail, _)| (tail, Token::Plus))
}

/// Parses a [`Token::Minus`] from `input`.
fn minus<T>(input: &str) -> LexResult<'_, T> {
    char('-').parse(input).map(|(tail, _)| (tail, Token::Minus))
}

/// Parses a [`Token::Equals`] from `input`.
fn equals<T>(input: &str) -> LexResult<'_, T> {
    char('=')
        .parse(input)
        .map(|(tail, _)| (tail, Token::Equals))
}

/// Parses a [`Token::LeftAngleBracket`] from `input`.
fn left_angle_bracket<T>(input: &str) -> LexResult<'_, T> {
    char('<')
        .parse(input)
        .map(|(tail, _)| (tail, Token::LeftAngleBracket))
}

/// Parses a [`Token::RightAngleBracket`] from `input`.
fn right_angle_bracket<T>(input: &str) -> LexResult<'_, T> {
    char('>')
        .parse(input)
        .map(|(tail, _)| (tail, Token::RightAngleBracket))
}

/// Parses a [`Token::Skip`] from `input`.
fn skip<T>(input: &str) -> LexResult<'_, T> {
    tag("skip")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Skip))
}

/// Parses a [`Token::If`] from `input`.
fn r#if<T>(input: &str) -> LexResult<'_, T> {
    tag("if").parse(input).map(|(tail, _)| (tail, Token::If))
}

/// Parses a [`Token::Then`] from `input`.
fn then<T>(input: &str) -> LexResult<'_, T> {
    tag("then")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Then))
}

/// Parses a [`Token::Else`] from `input`.
fn r#else<T>(input: &str) -> LexResult<'_, T> {
    tag("else")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Else))
}

/// Parses a [`Token::Fi`] from `input`.
fn fi<T>(input: &str) -> LexResult<'_, T> {
    tag("fi").parse(input).map(|(tail, _)| (tail, Token::Fi))
}

/// Parses a [`Token::While`] from `input`.
fn r#while<T>(input: &str) -> LexResult<'_, T> {
    tag("while")
        .parse(input)
        .map(|(tail, _)| (tail, Token::While))
}

/// Parses a [`Token::Do`] from `input`.
fn r#do<T>(input: &str) -> LexResult<'_, T> {
    tag("do").parse(input).map(|(tail, _)| (tail, Token::Do))
}

/// Parses a [`Token::Od`] from `input`.
fn od<T>(input: &str) -> LexResult<'_, T> {
    tag("od").parse(input).map(|(tail, _)| (tail, Token::Od))
}

/// Parses a [`Token::True`] from `input`.
fn r#true<T>(input: &str) -> LexResult<'_, T> {
    tag("true")
        .parse(input)
        .map(|(tail, _)| (tail, Token::True))
}

/// Parses a [`Token::False`] from `input`.
fn r#false<T>(input: &str) -> LexResult<'_, T> {
    tag("false")
        .parse(input)
        .map(|(tail, _)| (tail, Token::False))
}

/// Parses a [`Token::Not`] from `input`.
fn not<T>(input: &str) -> LexResult<'_, T> {
    tag("not").parse(input).map(|(tail, _)| (tail, Token::Not))
}

/// Parses a [`Token::And`] from `input`.
fn and<T>(input: &str) -> LexResult<'_, T> {
    tag("and").parse(input).map(|(tail, _)| (tail, Token::And))
}

/// Parses a [`Token::Or`] from `input`.
fn or<T>(input: &str) -> LexResult<'_, T> {
    tag("or").parse(input).map(|(tail, _)| (tail, Token::Or))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespace_parser_is_correct() {
        assert!(whitespace::<usize>(" \t\r hello").unwrap().0 == "hello");
        assert!(whitespace::<usize>("hello \t\r").is_err());
    }

    #[test]
    fn semicolon_parser_is_correct() {
        assert!(semicolon::<usize>(";").is_ok_and(|res| res == ("", Token::Semicolon)));
        assert!(semicolon::<usize>(";hjk").is_ok_and(|res| res == ("hjk", Token::Semicolon)));
        assert!(semicolon::<usize>("world;").is_err());
    }

    #[test]
    fn paren_parsers_are_correct() {
        assert!(left_paren::<usize>("(").is_ok_and(|res| res == ("", Token::LeftParen)));
        assert!(right_paren::<usize>(")").is_ok_and(|res| res == ("", Token::RightParen)));
    }

    #[test]
    fn skip_parser_is_correct() {
        assert!(skip::<usize>("skip").is_ok_and(|res| res == ("", Token::Skip)));
        assert!(skip::<usize>("junkskip").is_err());
    }

    #[test]
    fn assign_parser_is_correct() {
        assert!(assign::<usize>(":=").is_ok_and(|res| res == ("", Token::Assign)));
    }

    #[test]
    fn branch_parsers_are_correct() {
        assert!(r#if::<usize>("if").is_ok_and(|res| res == ("", Token::If)));
        assert!(then::<usize>("then").is_ok_and(|res| res == ("", Token::Then)));
        assert!(r#else::<usize>("else").is_ok_and(|res| res == ("", Token::Else)));
        assert!(fi::<usize>("fi").is_ok_and(|res| res == ("", Token::Fi)));
    }

    #[test]
    fn loop_parsers_are_correct() {
        assert!(r#while::<usize>("while").is_ok_and(|res| res == ("", Token::While)));
        assert!(r#do::<usize>("do").is_ok_and(|res| res == ("", Token::Do)));
        assert!(od::<usize>("od").is_ok_and(|res| res == ("", Token::Od)));
    }

    #[test]
    fn arithmetic_parsers_are_correct() {
        assert!(star::<usize>("*").is_ok_and(|res| res == ("", Token::Star)));
        assert!(plus::<usize>("+").is_ok_and(|res| res == ("", Token::Plus)));
        assert!(minus::<usize>("-").is_ok_and(|res| res == ("", Token::Minus)));
    }

}
