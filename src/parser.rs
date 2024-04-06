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
//! they can be converted into [`Ast`]s to provide an opaque interface.

pub mod aexp;
pub mod bexp;
pub mod cmd;
mod util;
