//! A compiler for the IMP language.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

#[macro_use]
extern crate static_assertions as sa;

pub mod ast;
pub mod int;
pub mod backend;
pub mod lexer;
pub mod parser;
pub mod relu;

fn main() {
    println!("hello, world!");
}
