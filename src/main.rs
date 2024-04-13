//! A compiler for the IMP programming language.

// LINTS
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use crate::cli::Cli;

extern crate static_assertions as sa;

pub mod ast;
pub mod backend;
pub mod cli;
pub mod int;
pub mod lexer;
pub mod parser;

fn main() -> anyhow::Result<()> {
    let options: Cli = argh::from_env();
    dbg!(options.clone());
    options.handle()
}
