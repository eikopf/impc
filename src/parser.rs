//! A [`nom`]-based parser operating on sequences of tokens.

// TODO: since we're basically operating on a fixed buffer of registers, are there
// available SSA optimisations?

mod util;

pub mod aexp;
pub mod bexp;
pub mod cmd;
