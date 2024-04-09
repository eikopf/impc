//! The [`Backend`] trait and corresponding implementations.

use crate::ast::Ast;

pub mod interpreter;

/// A trait for compiler backends which can consume [`Ast`]s and produce some IR.
pub trait Backend {
    /// The expected variable type of ASTs passed to this backend.
    type Var;
    /// The expected integer type of ASTs passed to this backend.
    type Int;
    /// The _internal representation_ used by this backend.
    type IR;

    /// Consumes the given `ast` and returns some backend-specific IR.
    fn process_ast(ast: Ast<Self::Var, Self::Int>) -> Self::IR;
}

/// A trait for compiler backends that can execute programs.
pub trait Executor: Backend {
    /// The result of executing a program with this backend.
    type Output;

    /// Executes the given `program` and produces some output.
    fn execute(program: Self::IR) -> Self::Output;
}
