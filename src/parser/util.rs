//! Common functionality for the [`crate::parser`] submodules.
//!
//! # Relationship to [`nom`]
//! Because most primitive [`nom`] parsers (e.g. [`nom::bytes::complete::tag`]) rely on the
//! [`nom::InputTake`] trait to describe the relationship between a sequence and its elements, it
//! is not possible to use these parsers with [`crate::lexer::token::Token`] slices. 
//!
//! Luckily, we only need to replace a small handful of these primitive parsers, and they can be
//! replaced in their entirety by the [`token`] and [`tokens`] functions (which act like
//! [`nom::bytes::complete::tag`] for individual tokens and token slices respectively).

use nom::{combinator::fail, error::ParseError, sequence::separated_pair, Parser};

/// Returns a [`Parser`] that matches the pair `(lhs, rhs)` separated
/// by `operator`, and then invokes `constructor` to produce a result
/// in the successful case.
#[inline(always)]
pub fn binary_expr<I, L, Op, R, O, E>(
    lhs: impl Parser<I, L, E> + Clone,
    operator: impl Parser<I, Op, E> + Clone,
    rhs: impl Parser<I, R, E> + Clone,
    constructor: impl FnOnce(L, R) -> O + Clone,
) -> impl Parser<I, O, E>
where
    E: ParseError<I>,
{
    move |input| {
        separated_pair(lhs.clone(), operator.clone(), rhs.clone())
            .parse(input)
            .map(|(tail, (lhs, rhs))| (tail, constructor.clone()(lhs, rhs)))
    }
}

/// Converts a binary function taking boxed parameters to a binary function taking owned parameters
#[inline(always)]
pub fn unbox2<L, R, O>(
    f: impl FnOnce(Box<L>, Box<R>) -> O + Clone,
) -> impl FnOnce(L, R) -> O + Clone {
    move |left, right| f.clone()(Box::new(left), Box::new(right))
}

/// Returns a [`Parser`] that matches on `t` when given some `[T]`.
pub fn token<'tok, 'src, T, E>(t: &'tok T) -> impl Parser<&'src [T], &T, E> + Clone
where
    'src: 'tok,
    T: 'src + PartialEq,
    E: ParseError<&'src [T]>,
{
    move |tokens: &'src [T]| match tokens.split_first() {
        Some((head, tail)) if head == t => Ok((tail, head)),
        _ => fail(tokens),
    }
}

/// Returns a [`Parser`] that matches on the sequence `t` when given some `[T]`.
pub fn tokens<'tok, 'src, T, E>(t: &'tok [T]) -> impl Parser<&'src [T], &'src [T], E> + Clone + 'tok
where
    'src: 'tok,
    T: 'src + PartialEq,
    E: ParseError<&'src [T]>,
{
    move |tokens: &'src [T]| {
        if t.len() > tokens.len() {
            fail(tokens)
        } else {
            match tokens.split_at(t.len()) {
                (head, tail) if head == t => Ok((tail, head)),
                _ => fail(tokens),
            }
        }
    }
}
