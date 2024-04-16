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
    // register custom panic handler
    better_panic::Settings::auto()
        .backtrace_first(false)
        .message("\nimpc panicked with the following error:")
        .lineno_suffix(true)
        .install();

    // parse cli arguments
    let args = argh::from_env::<cli::Cli>();

    // process arguments and execute accordingly
    cli::Cli::handle(args)
}
