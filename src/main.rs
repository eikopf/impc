//! A compiler for the IMP programming language.

// LINTS
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

extern crate static_assertions as sa;

pub mod ast;
pub mod backend;
pub mod cli;
pub mod int;
pub mod lexer;
pub mod parser;
pub mod tree;

fn main() -> anyhow::Result<()> {
    // reads arguments and passes them to handle()
    argh::from_env::<cli::Cli>().handle()
}
