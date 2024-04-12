//! The command-line interface for `impc`.
//!
//! Usage (as with any other [`argh`] interface) involves first invoking [`argh::from_env()`], and
//! then processing the resulting data (in this case an instance of [`Cli`]).

#![allow(missing_docs)]
#![allow(clippy::missing_docs_in_private_items)]
#![allow(dead_code)]

use std::{collections::HashMap, ffi::OsString, str::FromStr};

use argh::FromArgs;
use nom::{
    bytes::complete::tag,
    character::complete::{alphanumeric1, digit1, multispace0},
    combinator::{map_res, opt},
    error::Error,
    multi::separated_list0,
    sequence::{delimited, pair, separated_pair},
    Finish, Parser,
};

/// A compiler for the IMP programming language.
#[derive(Debug, FromArgs)]
pub struct Cli {
    #[argh(subcommand)]
    cmd: CliSubCommand,
}

impl Cli {
    /// Consumes `self` and processes the given subcommand.
    pub fn handle(self) -> anyhow::Result<()> {
        todo!();
    }
}

/// The set of the distinct subcommands available to be passed to the [`Cli`].
#[derive(Debug, FromArgs)]
#[argh(subcommand)]
enum CliSubCommand {
    /// The simplest possible invocation of `impc`, which runs a `.imp`
    /// file before printing the result and immediately exiting.
    Run(Run),
}

/// Runs an .imp file, optionally using the given backend and bindings. If bindings are not
/// provided, they will be assigned by an interactive prompt.
#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "run")]
struct Run {
    /// the chosen backend (defaults to interpreter)
    #[argh(option, short = 'b', default = "Backend::default()")]
    backend: Backend,

    /// a JSON-formatted list of variable bindings
    #[argh(option, long = "let", short = 'l')]
    bindings: Option<Bindings>,

    /// a path to an .imp file
    #[argh(positional)]
    file: OsString,
}

/// A simple set of marker values, corresponding to particular implementations
/// of the [`crate::backend::Backend`] trait.
#[derive(Debug, Default)]
enum Backend {
    /// Indicates that the selected backend is the [`interpreter`](crate::backend::interpreter).
    #[default]
    Interpreter,
    /// Indicates that the selected backend is the bytecode virtual machine.
    ByteCode,
}

impl FromStr for Backend {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "interpreter" => Ok(Self::Interpreter),
            "bytecode" => Ok(Self::ByteCode),
            other => Err(String::from(other)),
        }
    }
}

/// A set of name-value pairs that can be optionally provided to some subcommands,
/// thereby avoiding having to explicitly bind these values interactively.
#[derive(Debug)]
struct Bindings {
    /// The actual key-value pairs, mapping names to their bound values.
    map: HashMap<String, usize>,
}

impl FromStr for Bindings {
    type Err = Error<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        delimited(
            pair(tag("{"), opt(multispace0)),
            separated_list0(
                delimited(multispace0, tag(","), multispace0),
                separated_pair(
                    alphanumeric1,
                    delimited(multispace0, tag(":"), multispace0),
                    map_res(digit1, <usize>::from_str),
                ),
            ),
            pair(opt(multispace0), tag("}")),
        )
        .parse(s)
        .finish()
        .map(|(_, pairs)| Bindings {
            map: pairs
                .into_iter()
                .map(|(name, value)| (String::from(name), value))
                .collect::<HashMap<String, usize>>(),
        })
        .map_err(|err: Error<&str>| Error::new(String::from(err.input), err.code))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_bindings_parser() {
        let input = "{ X: 2,    \t\nY :3, \t\n\r Z   :\n 0  \t}";
        let bindings = Bindings::from_str(input).unwrap();
        assert_eq!(bindings.map.get("X"), Some(&2));
        assert_eq!(bindings.map.get("Y"), Some(&3));
        assert_eq!(bindings.map.get("Z"), Some(&0));
    }
}
