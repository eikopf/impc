//! Common functionality for the [`crate::parser`] submodules.

use nom::{
    bytes::complete::tag, error::ParseError, sequence::separated_pair, Compare, InputLength,
    InputTake, Parser,
};

/// Returns a [`Parser`] that matches the pair `(lhs, rhs)` separated
/// by `operator`, and then invokes `constructor` to produce a result
/// in the successful case.
///
/// # Generic Parameters
/// - `I` is the input type of the returned parser;
/// - `L` is the return type of `lhs`;
/// - `Op` is the type of `operator`;
/// - `R` is the return type of `rhs`;
/// - `O` is the return type of the returned parser;
/// - `E` is the error type of the returned parser.
#[inline(always)]
pub const fn binary_expr<I, L, Op, R, O, E>(
    lhs: impl Parser<I, L, E> + Copy,
    operator: Op,
    rhs: impl Parser<I, R, E> + Copy,
    constructor: impl FnOnce(L, R) -> O + Clone,
) -> impl Parser<I, O, E>
where
    Op: Clone + InputLength,
    I: Compare<Op> + InputTake,
    E: ParseError<I>,
{
    move |input| {
        separated_pair(lhs, tag(operator.clone()), rhs)
            .parse(input)
            .map(|(tail, (lhs, rhs))| (tail, constructor.clone()(lhs, rhs)))
    }
}

/// Converts a binary function taking boxed parameters to a binary function taking owned parameters
#[inline(always)]
pub const fn unbox2<L, R, O>(
    f: impl FnOnce(Box<L>, Box<R>) -> O + Clone,
) -> impl FnOnce(L, R) -> O + Clone {
    move |left, right| f.clone()(Box::new(left), Box::new(right))
}
