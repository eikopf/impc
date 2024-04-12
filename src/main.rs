//! A compiler for the IMP language.

#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use std::{
    collections::HashMap,
    io::{Read, Write},
};

use ast::{
    tree::{Evaluator, Tree},
    Ast,
};
use backend::interpreter::Interpreter;
use int::ImpSize;
use lexer::token::Tokens;
use num_traits::Num;

extern crate static_assertions as sa;

pub mod ast;
pub mod backend;
pub mod cli;
pub mod int;
pub mod lexer;
pub mod parser;
pub mod var;

fn main() {
    let input = {
        let mut buf = String::new();
        let _ = std::io::stdin().read_line(&mut buf).unwrap();
        buf
    };

    let tokens = Tokens::<'_, ImpSize>::try_from(input.as_ref()).unwrap();
    let ast = Ast::try_from(tokens.as_ref()).unwrap();
    let names = ast.names();

    let interpreter = {
        let mut bindings = HashMap::new();
        let sorted_names = {
            let mut names = names.into_iter().collect::<Vec<_>>();
            names.sort_unstable();
            names
        };

        for name in sorted_names {
            let mut buf = String::new();
            print!("Provide a binding for {name}: ");
            let _ = std::io::stdout().flush();
            let _ = std::io::stdin()
                .read_line(&mut buf)
                .expect("Could not read a valid string");
            let value = ImpSize::from_str_radix(&buf.trim(), 10)
                .expect("Could not parse input as an integer");
            bindings.insert(name.clone(), value);
        }

        Interpreter::from(bindings)
    };

    let result = interpreter.eval(&ast.root());

    println!();
    match result {
        Ok(state) => println!("Got result: {state:?}"),
        Err(err) => println!("Got error: {err}"),
    }
}
