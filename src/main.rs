//! A compiler for the IMP language.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

extern crate static_assertions as sa;

pub mod ast;
pub mod backend;
pub mod cli;
pub mod int;
pub mod lexer;
pub mod parser;
pub mod var;

fn main() -> anyhow::Result<()> {
    let impc: cli::Cli = argh::from_env();
    impc.handle()
}
