//! [`Ast`](super::Ast) rewriting and simplifying functionality.
//!
//! # Rewriting Rules
//! ## [Arithmetic Expressions](Aexp)
//! The following trivial rules hold for rewriting arithmetic expressions:
//!
//! 1. Variables and integers cannot be simplified;
//! 2. Binary expressions including `1` and `0` can be simplified in all cases;
//! 3. Binary expressions can be immediately simplified if both their arguments are integers.
//!
//! However, these do not cover all possible cases. Consider an expression like `(X + 1) + 1`, which
//! can be simplified to `X + 2`. The rules given above cannot do this, however, and so new rules
//! must be introduced:
//!
//! 4. Binary expressions whose arguments are distinct variables cannot be simplified;
//! 5. Binary expressions whose arguments are identical obey the following rules:
//!     - `X + X` can be simplified as `2 * X`;
//!     - `X - X` can be simplified as `0`;
//!     - `X * X` cannot be simplified in IMP.
//! 6. In general, binary expressions which include at least one integer can be used to simplify
//!    larger expressions according to the following rules:
//!     - `(X + a) + (Y + b)` can be simplified as `(X + Y) + (a + b)`;
//!     - `(X + a) * (Y + b)` can be simplified as `(X * Y) + (Y * a) + (X * b) + (a * b)`;
//!     - `(X * a) + (X * b)` can be simplified as `X * (a + b)`;
//!     - `(X * a) + (Y * a)` can be simplified as `(X + Y) * a`;
//!     - Simplifications involving the `-` operator are generally unsound, as IMP does not
//!     impelement subtraction in the usual sense.

use std::convert::Infallible;

use num_traits::{SaturatingSub, Unsigned};

use crate::{parser::aexp::Aexp, relu::relu};

use super::tree::{Evaluator, Tree};

/// A trait for rewriting [`Tree`]s.
///
/// # Blanket Implementations
/// A [`Rewriter`] is an [`Evaluator`] in the sense that it manipulates
/// a [`Tree`] into a different form, and moreover it is also a
/// [`StatelessEvaluator`](super::tree::StatelessEvaluator) in the sense
/// that it performs this manipulation without reference to external state.
///
/// When `Self::Output = T`, a [`Rewriter`] is also a [`Simplifier`]. This
/// is little more than a nice renaming, and indeed it is not possible to
/// implement [`Simplifier`] by any other means than the blanket implementation.
pub trait Rewriter<T>
where
    T: Tree,
{
    /// The return type of [`Rewriter::rewrite`].
    type Output;

    /// Rewrites the given `tree` into a new tree.
    fn rewrite(tree: T) -> Self::Output;
}

impl<T, A> Evaluator<(), T> for A
where
    A: Rewriter<T>,
    T: Tree,
{
    type Output = <A as Rewriter<T>>::Output;

    type Error = Infallible;

    #[inline(always)]
    fn evaluate(tree: T, _state: ()) -> Result<(Self::Output, ()), Self::Error> {
        Ok((Self::rewrite(tree), ()))
    }
}

/// A trait for _simplifying_ [`Tree`]s, which can only
/// be implemented by implementing [`Rewriter`] such
/// that `Rewriter::Output = T`.
pub trait Simplifier<T>: Rewriter<T, Output = T>
where
    T: Tree,
{
    /// Returns a simplified tree equivalent to the given `tree`.
    fn simplify(tree: T) -> T;
}

impl<T, A> Simplifier<T> for A
where
    A: Rewriter<T, Output = T>,
    T: Tree,
{
    #[inline(always)]
    fn simplify(tree: T) -> T {
        Self::rewrite(tree)
    }
}

/// A unit struct providing static methods for rewriting [`Ast`](super::Ast)s.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstRewriter;

impl<V, T> Rewriter<Aexp<V, T>> for AstRewriter
where
    T: Clone + Unsigned + SaturatingSub,
    V: Clone + PartialEq,
{
    type Output = Aexp<V, T>;

    fn rewrite(tree: Aexp<V, T>) -> Self::Output {
        match tree {
            // integers and variables are just immediately returned
            int @ Aexp::Int(_) => int,
            var @ Aexp::Var(_) => var,
            // subtraction expression folding
            Aexp::Sub(lhs, rhs) => match (*lhs, *rhs) {
                // both args are integers
                (Aexp::Int(a), Aexp::Int(b)) => Aexp::Int(relu(&a, &b)),
                // identical arguments
                (a, b) if a == b => Aexp::Int(T::zero()),
                // first argument is zero
                (Aexp::Int(x), _) if x.is_zero() => Aexp::Int(T::zero()),
                // second argument is zero
                (arg, Aexp::Int(x)) if x.is_zero() => arg,
                // otherwise just recurse
                other => Aexp::Sub(
                    Box::new(Self::rewrite(other.0)),
                    Box::new(Self::rewrite(other.1)),
                ),
            },
            // multiplication expression folding
            Aexp::Mul(lhs, rhs) => match (Self::rewrite(*lhs), Self::rewrite(*rhs)) {
                // both args are integers
                (Aexp::Int(a), Aexp::Int(b)) => Aexp::Int(a * b),
                // at least one argument is 0
                (Aexp::Int(x), _) | (_, Aexp::Int(x)) if x.is_zero() => Aexp::Int(T::zero()),
                // at least one argument is 1
                (Aexp::Int(x), arg) | (arg, Aexp::Int(x)) if x.is_one() => arg,
                // expression has the binomial form (a + b) * (c + d),
                // which can be rewritten as (a * c) + (c * b) + (a * d) + (b * d)
                (Aexp::Add(a, b), Aexp::Add(c, d)) => Self::rewrite(Aexp::Add(
                    Box::new(Aexp::Mul(a.clone(), c.clone())),
                    Box::new(Aexp::Add(
                        Box::new(Aexp::Mul(b.clone(), c)),
                        Box::new(Aexp::Add(
                            Box::new(Aexp::Mul(a, d.clone())),
                            Box::new(Aexp::Mul(b, d)),
                        )),
                    )),
                )),
                // default case
                other => match other {
                    // if the int is on the left, swap their ordering
                    (int @ Aexp::Int(_), var @ Aexp::Var(_)) => {
                        Aexp::Mul(Box::new(var), Box::new(int))
                    }
                    // otherwise they're arbitrary expressions, and we return
                    _ => Aexp::Mul(Box::new(other.0), Box::new(other.1)),
                },
            },
            // add expression folding
            Aexp::Add(lhs, rhs) => match (Self::rewrite(*lhs), Self::rewrite(*rhs)) {
                // both args are integers
                (Aexp::Int(a), Aexp::Int(b)) => Aexp::Int(a + b),
                // identical variables, i.e. `x + x` becomes `x * 2`
                (Aexp::Var(argl), Aexp::Var(argr)) if argl == argr => Aexp::Mul(
                    Box::new(Aexp::Var(argl)),
                    Box::new(Aexp::Int(T::one() + T::one())),
                ),
                // form of (VAR + INT) + INT or INT + (VAR + INT)
                (Aexp::Add(a, b), c @ Aexp::Int(_)) | (c @ Aexp::Int(_), Aexp::Add(a, b))
                    if is_var(&a) && is_int(&b) =>
                {
                    Aexp::Add(a, Box::new(Self::rewrite(Aexp::Add(b, Box::new(c)))))
                }
                // at least one argument is 0
                (Aexp::Int(x), arg) | (arg, Aexp::Int(x)) if x.is_zero() => arg,
                // addition of addition (i.e. quaternary addition), where
                // by construction the permutation (1342) can simplify the
                // expression without breaking the left-VAR property
                (Aexp::Add(a, b), Aexp::Add(c, d)) => Aexp::Add(
                    Box::new(Self::rewrite(Aexp::Add(a, c))),
                    Box::new(Self::rewrite(Aexp::Add(d, b))),
                ),
                // left (reverse) distributive property
                (Aexp::Mul(a, b), Aexp::Mul(c, d)) if a == c => {
                    Aexp::Mul(a, Box::new(Aexp::Add(b, d)))
                }
                // right (reverse) distributive property
                (Aexp::Mul(a, b), Aexp::Mul(c, d)) if b == d => {
                    Aexp::Mul(Box::new(Aexp::Add(a, c)), b)
                }
                // default case
                other => match other {
                    (int @ Aexp::Int(_), var @ Aexp::Var(_)) => {
                        Aexp::Add(Box::new(var), Box::new(int))
                    }
                    _ => Aexp::Add(Box::new(other.0), Box::new(other.1)),
                },
            },
        }
    }
}

/// Returns `true` iff `expr` is an [`Aexp::Var`].
const fn is_var<V, T>(expr: &Aexp<V, T>) -> bool {
    matches!(expr, Aexp::Var(_))
}

/// Returns `true` iff `expr` is an [`Aexp::Int`].
const fn is_int<V, T>(expr: &Aexp<V, T>) -> bool {
    matches!(expr, Aexp::Int(_))
}

#[cfg(test)]
mod tests {
    use crate::{lexer::token::Tokens, parser::aexp::aexp};

    use super::*;

    #[test]
    fn check_aexp_rewriter_impl() {
        // expr = (+ 1 (+ 2 (+ 3 4))), equivalent to 10
        let tokens: Tokens = "1 + 2 + 3 + 4".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("raw aexp: {expr}");
        let expr = AstRewriter::rewrite(expr);
        eprintln!("rewritten aexp: {expr}");
        assert_eq!(expr, Aexp::Int(10));

        // expr = (+ (+ 1 X) (+ 3 4)), equivalent to (+ X 8)
        let tokens: Tokens = "(1 + X) + 3 + 4".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("raw aexp: {expr}");
        let expr = AstRewriter::rewrite(expr);
        eprintln!("rewritten aexp: {expr}");
        assert_eq!(
            expr,
            Aexp::Add(Box::new(Aexp::var_from("X")), Box::new(Aexp::Int(8)))
        );

        // expr = (+ (- 1 X) (+ 3 4)), equivalent to (+ (- 1 X) 7)
        // note that it is _not_ sound to rewrite expr as (- 8 X),
        // since the `-` operator performs nonstandard subtraction
        let tokens: Tokens = "(1 - X) + 3 + 4".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("raw aexp: {expr}");
        let expr = AstRewriter::rewrite(expr);
        eprintln!("rewritten aexp: {expr}");
        assert_eq!(
            expr,
            Aexp::Add(
                Box::new(Aexp::Sub(
                    Box::new(Aexp::Int(1)),
                    Box::new(Aexp::var_from("X"))
                )),
                Box::new(Aexp::Int(7))
            )
        );

        let tokens: Tokens = "((1 * X) + 3) * 4".try_into().unwrap();
        let (_, expr): (_, Aexp<_>) = aexp(tokens.as_ref()).unwrap();
        eprintln!("raw aexp: {expr}");
        let expr = AstRewriter::rewrite(expr);
        eprintln!("rewritten aexp: {expr}");
        assert_eq!(
            expr,
            Aexp::Mul(
                Box::new(Aexp::Add(
                    Box::new(Aexp::var_from("X")),
                    Box::new(Aexp::Int(3))
                )),
                Box::new(Aexp::Int(4)),
            )
        );
    }
}
