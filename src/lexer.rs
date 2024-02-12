//! Streaming lexer for `.imp` files.

use byteyarn::YarnBox;
use nom::{
    branch::alt,
    bytes::streaming::{tag, take_while},
    character::{
        is_alphanumeric,
        streaming::{char, multispace1, u64},
    },
    combinator::{all_consuming, verify},
    error::VerboseError,
    multi::many0,
    Finish, IResult, Parser,
};

/// A token generated by parsing valid IMP source code.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'str> {
    /// A sequence accepted by `[ \t\r\n]+`.
    Whitespace,
    /// A single semicolon (`;`).
    Semicolon,
    /// A single left parenthesis (`(`).
    LeftParen,
    /// A single right parenthesis (`)`).
    RightParen,
    /// The `skip` keyword.
    Skip,
    /// The assignment operator (`:=`).
    Assign,
    /// A single asterisk (`*`).
    Star,
    /// A single plus sign (`+`).
    Plus,
    /// A single minus sign (`-`).
    Minus,
    /// The `if` keyword.
    If,
    /// The `then` keyword.
    Then,
    /// The `else` keyword.
    Else,
    /// The `fi` keyword.
    Fi,
    /// The `while` keyword.
    While,
    /// The `do` keyword.
    Do,
    /// The `od` keyword.
    Od,
    /// The `true` keyword.
    True,
    /// The `false` keyword.
    False,
    /// A single equals sign (`=`).
    Equals,
    /// A single left angle bracket (`<`).
    LeftAngleBracket,
    /// A single right angle bracket (`>`).
    RightAngleBracket,
    /// The `not` keyword.
    Not,
    /// The `and` keyword,
    And,
    /// The `or` keyword,
    Or,
    /// A variable name.
    Var(Var<'str>),
    /// An integer value.
    Int(u64),
}

/// A valid IMP variable, guaranteed to begin
/// with a latin character and to have a body
/// composed of latin characters, arabic numerals,
/// and underscores.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Var<'str>(YarnBox<'str, str>);

impl<'a> Var<'a> {
    /// Returns a reference to the underlying [`YarnBox`].
    pub fn get(&self) -> &YarnBox<'a, str> {
        &self.0
    }
}

/// The general return type for [`crate::lexer`] parsers.
pub type LexResult<'src> = IResult<&'src str, Token<'src>, VerboseError<&'src str>>;

/// Attempts to parse the entirety of `input` into a `Vec<Token<'_>>`,
/// either returning it completely or producing a [`VerboseError`].
pub fn parse_tokens(input: &str) -> Result<Vec<Token<'_>>, VerboseError<String>> {
    all_consuming(many0(alt((
        whitespace,
        skip,
        semicolon,
        left_paren,
        right_paren,
        left_angle_bracket,
        right_angle_bracket,
        assign,
        branch_keyword,
        loop_keyword,
        arithmetic_operator,
        r#true,
        r#false,
        equals,
        not,
        and,
        or,
        var,
        int,
    ))))
    .parse(input)
    .finish()
    .map(|(_tail, vec)| {
        debug_assert!(_tail.is_empty());
        vec
    })
    .map_err(|err| VerboseError {
        errors: err
            .errors
            .into_iter()
            .map(|(s, kind)| (s.to_owned(), kind))
            .collect(),
    })
}

/// Parses a [`Token::Whitespace`] from `input`.
fn whitespace(input: &str) -> LexResult<'_> {
    multispace1(input).map(|(tail, _)| (tail, Token::Whitespace))
}

/// Parses a [`Token::Semicolon`] from `input`.
fn semicolon(input: &str) -> LexResult<'_> {
    char(';')
        .parse(input)
        .map(|(tail, _)| (tail, Token::Semicolon))
}

/// Parses a [`Token::LeftParen`] from `input`.
fn left_paren(input: &str) -> LexResult<'_> {
    char('(')
        .parse(input)
        .map(|(tail, _)| (tail, Token::LeftParen))
}

/// Parses a [`Token::RightParen`] from `input`.
fn right_paren(input: &str) -> LexResult<'_> {
    char(')')
        .parse(input)
        .map(|(tail, _)| (tail, Token::RightParen))
}

/// Parses a [`Token::Skip`] from `input`.
fn skip(input: &str) -> LexResult<'_> {
    tag("skip")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Skip))
}

/// Parses a [`Token::Assign`] from `input`.
fn assign(input: &str) -> LexResult<'_> {
    tag(":=")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Assign))
}

/// Parses one of the three arithmetic operators (`*`, `+`, `-`)
/// from `input`.
fn arithmetic_operator(input: &str) -> LexResult<'_> {
    alt((star, plus, minus)).parse(input)
}

/// Parses a [`Token::Star`] from `input`.
fn star(input: &str) -> LexResult<'_> {
    char('*').parse(input).map(|(tail, _)| (tail, Token::Star))
}

/// Parses a [`Token::Plus`] from `input`.
fn plus(input: &str) -> LexResult<'_> {
    char('+').parse(input).map(|(tail, _)| (tail, Token::Plus))
}

/// Parses a [`Token::Minus`] from `input`.
fn minus(input: &str) -> LexResult<'_> {
    char('-').parse(input).map(|(tail, _)| (tail, Token::Minus))
}

/// Parses one of any of the branching keywords.
fn branch_keyword(input: &str) -> LexResult<'_> {
    alt((r#if, then, r#else, fi)).parse(input)
}

/// Parses a [`Token::If`] from `input`.
fn r#if(input: &str) -> LexResult<'_> {
    tag("if").parse(input).map(|(tail, _)| (tail, Token::If))
}

/// Parses a [`Token::Then`] from `input`.
fn then(input: &str) -> LexResult<'_> {
    tag("then")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Then))
}

/// Parses a [`Token::Else`] from `input`.
fn r#else(input: &str) -> LexResult<'_> {
    tag("else")
        .parse(input)
        .map(|(tail, _)| (tail, Token::Else))
}

/// Parses a [`Token::Fi`] from `input`.
fn fi(input: &str) -> LexResult<'_> {
    tag("fi").parse(input).map(|(tail, _)| (tail, Token::Fi))
}

/// Parses one of any of the looping keywords.
fn loop_keyword(input: &str) -> LexResult<'_> {
    alt((r#while, r#do, od)).parse(input)
}

/// Parses a [`Token::While`] from `input`.
fn r#while(input: &str) -> LexResult<'_> {
    tag("while")
        .parse(input)
        .map(|(tail, _)| (tail, Token::While))
}

/// Parses a [`Token::Do`] from `input`.
fn r#do(input: &str) -> LexResult<'_> {
    tag("do").parse(input).map(|(tail, _)| (tail, Token::Do))
}

/// Parses a [`Token::Od`] from `input`.
fn od(input: &str) -> LexResult<'_> {
    tag("od").parse(input).map(|(tail, _)| (tail, Token::Od))
}

/// Parses a [`Token::True`] from `input`.
fn r#true(input: &str) -> LexResult<'_> {
    tag("true")
        .parse(input)
        .map(|(tail, _)| (tail, Token::True))
}

/// Parses a [`Token::False`] from `input`.
fn r#false(input: &str) -> LexResult<'_> {
    tag("false")
        .parse(input)
        .map(|(tail, _)| (tail, Token::False))
}

/// Parses a [`Token::Equals`] from `input`.
fn equals(input: &str) -> LexResult<'_> {
    char('=')
        .parse(input)
        .map(|(tail, _)| (tail, Token::Equals))
}

/// Parses a [`Token::LeftAngleBracket`] from `input`.
fn left_angle_bracket(input: &str) -> LexResult<'_> {
    char('<')
        .parse(input)
        .map(|(tail, _)| (tail, Token::LeftAngleBracket))
}

/// Parses a [`Token::RightAngleBracket`] from `input`.
fn right_angle_bracket(input: &str) -> LexResult<'_> {
    char('>')
        .parse(input)
        .map(|(tail, _)| (tail, Token::RightAngleBracket))
}

/// Parses a [`Token::Not`] from `input`.
fn not(input: &str) -> LexResult<'_> {
    tag("not").parse(input).map(|(tail, _)| (tail, Token::Not))
}

/// Parses a [`Token::And`] from `input`.
fn and(input: &str) -> LexResult<'_> {
    tag("and").parse(input).map(|(tail, _)| (tail, Token::And))
}

/// Parses a [`Token::Or`] from `input`.
fn or(input: &str) -> LexResult<'_> {
    tag("or").parse(input).map(|(tail, _)| (tail, Token::Or))
}

/// Parses a [`Token::Var`] from `input`.
fn var(input: &str) -> LexResult<'_> {
    verify(
        take_while(|c: char| is_alphanumeric(c as u8) || c == '_'),
        |s: &str| !s.starts_with('_'),
    )
    .parse(input)
    .map(|(tail, name)| (tail, Token::Var(Var(YarnBox::from(name)))))
}

/// Parses a [`Token::Int`] from `input`.
fn int(input: &str) -> LexResult<'_> {
    u64.parse(input)
        .map(|(tail, value)| (tail, Token::Int(value)))
}
