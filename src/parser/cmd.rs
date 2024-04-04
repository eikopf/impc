//! The _commands_ (i.e. statements) that make up IMP programs.
//!
//! # Grammar
//! As originally given in an ANTLR4 `.g4` file (see below), the `cmd` grammar
//! was a purely tree-based structure with sequencing handled by the binary
//! `Sequence` variant.
//!
//! ```antlr
//! cmd  : 'skip'                                                               #Skip
//!      | variable=VAR ':=' expression=aexp                                    #Assignment
//!      | first=cmd ';' second=cmd                                             #Sequence
//!      | 'if' condition=bexp 'then' truecase=cmd 'else' falsecase=cmd 'fi'    #If
//!      | 'while' condition=bexp 'do' body=cmd 'od'                            #While
//!      ;
//! ```
//!
//! This is a neat definition, but causes unnecessary pointer indirection in an
//! equivalent implementation; hence in this compiler programs are given by lists
//! of commands and the `Sequence` variant has been omitted from the definition of
//! [`Cmd`].

use nom::{branch::alt, combinator::fail, IResult, Parser};

use crate::lexer::{
    token::{Token, TokensRef},
    var::Var,
};

use super::{
    aexp::{aexp, Aexp},
    bexp::Bexp,
    util::binary_expr,
};

/// An individual IMP command.
pub enum Cmd<'src, T = usize> {
    /// A no-op command, corresponding to [`Token::Skip`].
    Skip,
    /// A variable assignment command, corresponding to [`Token::Assign`].
    Assign(Var<'src>, Aexp<'src, T>),
    /// A conditional command, introduced by [`Token::If`] and [`Token::Then`],
    /// and terminated by [`Token::Fi`]. The first [`Aexp`] is the `true` branch,
    /// while the second is the `false` branch.
    If(Bexp<'src, T>, Aexp<'src, T>, Aexp<'src, T>),
    /// An iteration command, introduced by [`Token::While`] and [`Token::Do`], and
    /// terminated by [`Token::Od`].
    While(Bexp<'src, T>, Aexp<'src, T>),
}

/// The normal return type of parsers in the [`crate::parser::cmd`] module.
pub type CmdResult<'buf, 'src, T> = IResult<TokensRef<'buf, 'src, T>, Cmd<'src, T>>;

/// Parses an individual [`Cmd`] from `input`.
pub fn cmd<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    alt((r#while, r#if, assign, skip)).parse(input)
}

/// Parses a [`Cmd::Skip`] from `input`.
fn skip<'buf, 'src, T>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::Skip, tail)) => Ok((tail.into(), Cmd::Skip)),
        _ => fail(input),
    }
}

/// Parses a [`Cmd::Assign`] from `input`.
fn assign<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    binary_expr(var, Token::Assign, aexp, Cmd::Assign).parse(input)
}

/// Parses a [`Cmd::If`] from `input`.
fn r#if<'buf, 'src, T>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    todo!()
}

/// Parses a [`Cmd::While`] from `input`.
fn r#while<'buf, 'src, T>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    todo!()
}

/// Parses a [`Var`] from `input` by extracting from a [`Token::Var`].
fn var<'buf, 'src, T>(
    input: TokensRef<'buf, 'src, T>,
) -> IResult<TokensRef<'buf, 'src, T>, Var<'src>> {
    match input.split_first() {
        Some((Token::Var(var), tail)) => Ok((tail.into(), var.clone())),
        _ => fail(input),
    }
}
