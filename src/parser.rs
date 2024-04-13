//! A [`nom`]-based parser operating on sequences of tokens.
//!
//! # Expressions
//! IMP defines two distinct kinds of expressions: _arithmetic_ and _boolean_. These
//! have been reified into the [`aexp::Aexp`] and [`bexp::Bexp`] enums, which define
//! tree-like structures that explicitly model these expressions.
//!
//! # Commands
//! In the IMP grammar, a _command_ corresponds to a node in a program's abstract
//! syntax tree. These nodes are modelled by the [`cmd::Cmd`] enum, and in turn
//! they can be converted into [`crate::ast::Ast`]s to provide an opaque interface.

use nom::error::Error;

use crate::lexer::token::Token;

pub mod aexp;
pub mod bexp;
pub mod cmd;
pub mod expr;
mod util;

/// The input type consumed by all parsers in the [`crate::parser`] module.
pub type ParserInput<'buf, 'src, T> = &'buf [Token<&'src str, T>];

/// The error type produced by all parsers in the [`crate::parser`] module.
pub type ParserError<'buf, 'src, T> = Error<ParserInput<'buf, 'src, T>>;
