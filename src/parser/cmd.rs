//! The _commands_ (i.e. statements) that make up IMP programs.
//!
//! # Grammar
//! As originally given in an ANTLR4 `.g4` file (see below), the `cmd` grammar
//! was a purely tree-based structure with sequencing handled by the binary
//! `Sequence` variant.
//!
//! ```antlr
//! cmd  : 'skip'                                                               #Skip
//!      | variable=VAR ':=' expression=aexp                                    #Assignment
//!      | first=cmd ';' second=cmd                                             #Sequence
//!      | 'if' condition=bexp 'then' truecase=cmd 'else' falsecase=cmd 'fi'    #If
//!      | 'while' condition=bexp 'do' body=cmd 'od'                            #While
//!      ;
//! ```
//!
//! An important detail of this grammar is the `Sequence` variant, which is a
//! source of ambiguity (and hence potential unbounded left recursion). Consider
//! that, for an arbitrary program, it may have multiple valid syntax trees based
//! on which `Sequence` node is chosen to be the root of its tree.
//!
//! The solution here was to fix the choice of tree-structure: all IMP ASTs in
//! this compiler are (parsed by default as) right-balanced, such that no `Sequence`
//! node is ever the direct left-child of another `Sequence` node. This choice
//! corresponds to a change in the grammar (see below), introducing the `precedent`
//! term and setting it as the prefix for the `Sequence` variant.
//!
//! ```raw
//! cmd ::=
//!       precedent `;` cmd
//!     | `while` bexp `do` cmd `od`
//!     | `if` bexp `then` cmd `else` cmd `fi`
//!     | variable `:=` aexp
//!     | `skip`
//!
//! precedent ::=
//!       `while` bexp `do` cmd `od`
//!     | `if` bexp `then` cmd `else` cmd `fi`
//!     | variable `:=` aexp
//!     | `skip`
//!
//! ... other terms omitted ...
//! ```

use nom::{
    branch::alt,
    bytes::complete::tag,
    combinator::fail,
    sequence::{delimited, separated_pair},
    IResult, Parser,
};

use crate::lexer::{
    token::{Token, TokensRef},
    var::Var,
};

use super::{
    aexp::{aexp, Aexp},
    bexp::{bexp, Bexp},
    util::{binary_expr, unbox2},
};

/// An IMP command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Cmd<'src, T = usize> {
    /// A no-op command, corresponding to [`Token::Skip`].
    Skip,
    /// A variable assignment command, corresponding to [`Token::Assign`].
    Assign(Var<'src>, Aexp<'src, T>),
    /// A (left-to-right) sequence of two IMP commands.
    Seq(Box<Cmd<'src, T>>, Box<Cmd<'src, T>>),
    /// A conditional command, introduced by [`Token::If`] and [`Token::Then`],
    /// and terminated by [`Token::Fi`].
    If {
        /// The boolean condition that appears between [`Token::If`] and [`Token::Then`].
        cond: Bexp<'src, T>,
        /// The [`Cmd`] to be executed if `cond` evaluates to `true`.
        true_case: Box<Cmd<'src, T>>,
        /// The [`Cmd`] to be executed if `cond` evaluates to `false`.
        false_case: Box<Cmd<'src, T>>,
    },
    /// An iteration command, introduced by [`Token::While`] and [`Token::Do`], and
    /// terminated by [`Token::Od`].
    While(Bexp<'src, T>, Box<Cmd<'src, T>>),
}

impl<'src, T: std::fmt::Display> std::fmt::Display for Cmd<'src, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Skip => format!("(skip)"),
                Self::Assign(var, expr) => format!("(assign {var} {expr})"),
                Self::Seq(first, second) => format!("{first}\n{second}"),
                Self::While(cond, inner) => format!(
                    "(loop (while {cond})\n\t{0})",
                    format!("{inner}").replace("\n", "\n\t")
                ),
                Self::If {
                    cond,
                    true_case,
                    false_case,
                } => format!(
                    "(if {cond}\n\t{0}\n\t{1})",
                    format!("({true_case})").replace("\n", "\n\t"),
                    format!("({false_case})").replace("\n", "\n\t")
                ),
            }
        )
    }
}

/// The normal return type of parsers in the [`crate::parser::cmd`] module.
pub type CmdResult<'buf, 'src, T> = IResult<TokensRef<'buf, 'src, T>, Cmd<'src, T>>;

/// Parses an individual [`Cmd`] from `input`.
pub fn cmd<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    alt((seq, r#while, r#if, assign, skip)).parse(input)
}

/// Parses a non-[`Cmd::Seq`] [`Cmd`] from `input`.
///
/// This parser exists to be the prefix (i.e. `lhs`) for the [`seq`]
/// parser, since otherwise just using [`cmd`] results in unbounded
/// left recursion.
fn precedent<'buf, 'src, T: Clone + Eq>(
    input: TokensRef<'buf, 'src, T>,
) -> CmdResult<'buf, 'src, T> {
    alt((r#while, r#if, assign, skip)).parse(input)
}

/// Parses a [`Cmd::Seq`] from `input`.
fn seq<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    // it's a bit ugly to use the binary_expr combinator here, but it saves some code repitition
    binary_expr(precedent, Token::Semicolon, cmd, unbox2(Cmd::Seq)).parse(input)
}

/// Parses a [`Cmd::Skip`] from `input`.
fn skip<'buf, 'src, T>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    match input.split_first() {
        Some((Token::Skip, tail)) => Ok((tail.into(), Cmd::Skip)),
        _ => fail(input),
    }
}

/// Parses a [`Cmd::Assign`] from `input`.
fn assign<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    binary_expr(var, Token::Assign, aexp, Cmd::Assign).parse(input)
}

/// Parses a [`Cmd::If`] from `input`.
fn r#if<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    delimited(
        tag(Token::If),
        separated_pair(
            bexp,
            tag(Token::Then),
            separated_pair(cmd, tag(Token::Else), cmd),
        ),
        tag(Token::Fi),
    )
    .parse(input)
    .map(|(tail, (cond, (true_case, false_case)))| {
        (
            tail,
            Cmd::If {
                cond,
                true_case: Box::new(true_case),
                false_case: Box::new(false_case),
            },
        )
    })
}

/// Parses a [`Cmd::While`] from `input`.
fn r#while<'buf, 'src, T: Clone + Eq>(input: TokensRef<'buf, 'src, T>) -> CmdResult<'buf, 'src, T> {
    delimited(
        tag(Token::While),
        separated_pair(bexp, tag(Token::Do), cmd),
        tag(Token::Od),
    )
    .parse(input)
    .map(|(tail, (cond, inner))| (tail, Cmd::While(cond, Box::new(inner))))
}

/// Parses a [`Var`] from `input` by extracting from a [`Token::Var`].
fn var<'buf, 'src, T>(
    input: TokensRef<'buf, 'src, T>,
) -> IResult<TokensRef<'buf, 'src, T>, Var<'src>> {
    match input.split_first() {
        Some((Token::Var(var), tail)) => Ok((tail.into(), var.clone())),
        _ => fail(input),
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::Tokens;

    use super::*;

    #[test]
    fn check_cmd_parser() {
        let tokens: Tokens<'_> = "X := 0; Y := 1; Z := 2".try_into().unwrap();
        let (tail, program) = cmd(tokens.as_ref()).unwrap();
        eprintln!("{program}");

        assert!(tail.is_empty());
        assert_eq!(
            program,
            Cmd::Seq(
                Box::new(Cmd::Assign("X".into(), Aexp::Int(0))),
                Box::new(Cmd::Seq(
                    Box::new(Cmd::Assign("Y".into(), Aexp::Int(1))),
                    Box::new(Cmd::Assign("Z".into(), Aexp::Int(2)))
                ))
            )
        );

        let tokens: Tokens = "Y := 3; while X <> Y do X := Y; Y := 0; Z := X + Y od; Z := 4"
            .try_into()
            .unwrap();
        let (tail, program) = cmd(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), program.clone());
        eprintln!("{program}");

        assert!(tail.is_empty());
        assert_eq!(
            program,
            Cmd::Seq(
                Box::new(Cmd::Assign("Y".into(), Aexp::Int(3))),
                Box::new(Cmd::Seq(
                    Box::new(Cmd::While(
                        Bexp::NotEq(Aexp::Var("X".into()), Aexp::Var("Y".into())),
                        Box::new(Cmd::Seq(
                            Box::new(Cmd::Assign("X".into(), Aexp::Var("Y".into()))),
                            Box::new(Cmd::Seq(
                                Box::new(Cmd::Assign("Y".into(), Aexp::Int(0))),
                                Box::new(Cmd::Assign(
                                    "Z".into(),
                                    Aexp::Add(
                                        Box::new(Aexp::Var("X".into())),
                                        Box::new(Aexp::Var("Y".into()))
                                    )
                                ))
                            ))
                        ))
                    )),
                    Box::new(Cmd::Assign("Z".into(), Aexp::Int(4)))
                ))
            )
        );

        let tokens: Tokens = "if X < 13 then skip; skip; skip else Y := Y - 1 fi"
            .try_into()
            .unwrap();
        let (tail, program) = cmd(tokens.as_ref()).unwrap();
        dbg!(tail.clone(), program.clone());
        eprintln!("{program}");

        assert!(tail.is_empty());
        assert_eq!(
            program,
            Cmd::If {
                cond: Bexp::LessThan(Aexp::Var("X".into()), Aexp::Int(13)),
                true_case: Box::new(Cmd::Seq(
                    Box::new(Cmd::Skip),
                    Box::new(Cmd::Seq(Box::new(Cmd::Skip), Box::new(Cmd::Skip)))
                )),
                false_case: Box::new(Cmd::Assign(
                    "Y".into(),
                    Aexp::Sub(Box::new(Aexp::Var("Y".into())), Box::new(Aexp::Int(1)))
                )),
            }
        );
    }
}
