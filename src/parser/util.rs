//! Common functionality for the [`crate::parser`] submodules.

use nom::{
    bytes::complete::tag, error::ParseError, sequence::separated_pair, Compare, InputLength, Parser,
};

use crate::lexer::token::TokensRef;

/// Returns a [`Parser`] that matches the pair `(lhs, rhs)` separated
/// by `operator`, and then invokes `constructor` to produce a result
/// in the successful case.
///
/// # Generic Parameters
/// - `'buf` and `'src` are the lifetime parameters of the argument to the returned parser;
/// - `T` is the operant type of the argument to the returned parser;
/// - `L` is the return type of `lhs`;
/// - `Op` is the type of `operator`;
/// - `R` is the return type of `rhs`;
/// - `Out` is the return type of the returned parser;
/// - `E` is the error type of the returned parser.
#[inline(always)]
pub const fn binary_expr<'buf, 'src, T, L, Op, R, Out, E>(
    lhs: impl Parser<TokensRef<'buf, 'src, T>, L, E> + Copy,
    operator: Op,
    rhs: impl Parser<TokensRef<'buf, 'src, T>, R, E> + Copy,
    constructor: impl FnOnce(L, R) -> Out + Clone,
) -> impl Parser<TokensRef<'buf, 'src, T>, Out, E>
where
    'src: 'buf,
    T: 'buf + Clone,
    Op: Clone + InputLength,
    TokensRef<'buf, 'src, T>: Compare<Op>,
    E: ParseError<TokensRef<'buf, 'src, T>>,
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
) -> impl FnMut(L, R) -> O + Clone {
    move |left, right| f.clone()(Box::new(left), Box::new(right))
}
