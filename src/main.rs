//! A compiler for the IMP language.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod relu;

fn main() {
    println!("hello, world!");
}
