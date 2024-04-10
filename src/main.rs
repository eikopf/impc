//! A compiler for the IMP language.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

extern crate static_assertions as sa;

pub mod ast;
pub mod int;
pub mod var;
pub mod backend;
pub mod lexer;
pub mod parser;

fn main() {
    println!("hello, world!");
}
