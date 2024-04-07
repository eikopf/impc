//! Traits and functions modelling tree-structure.

/// A trait generalising tree-structure.
pub trait Tree {
    /// The type of the nodes in this tree.
    type Node;

    /// Consumes `self` and returns its root.
    fn root(self) -> Self::Node;

    /// Consumes `self` and maps `op` over it.
    fn map<U, F>(self, op: F) -> U
    where
        F: FnOnce(Self::Node) -> U;
}

/// A trait for trees with countable nodes.
pub trait NodeCount<T> where Self: Tree {
    /// Returns the number of nodes in `self`.
    fn count_nodes(&self) -> T;
}

/// A trait for evaluating trees.
///
/// # Auto-implementations
/// - [`PureEvaluator`] is automatically implemented if `S` is a reference type;
/// - [`StatelessEvaluator`] is automatically implemented if `S = ()`.
pub trait Evaluator<S, T>
where
    T: Tree,
{
    /// The type of the evaluation produced by
    /// the [`Evaluator::evaluate`] method.
    type Output;

    /// The error type of the [`Evaluator::evaluate`] method.
    type Error;

    /// Evaluates[^1] the given `tree` based on the given `state`, producing
    /// (in the success case) some output and the possibly-updated state.
    ///
    /// [^1]: For some meaningful interpretation of _evaluation_ with respect
    /// to `T`; typically this is in the sense of an AST.
    fn evaluate(tree: T, state: S) -> Result<(Self::Output, S), Self::Error>;
}

/// A trait for evaluating trees without altering the provided state.
pub trait PureEvaluator<'s, S, T>
where
    Self: Evaluator<&'s S, T>,
    T: Tree,
    S: 's,
{
    /// Evaluates the given `tree` based on the given `state` reference.
    fn evaluate_pure(tree: T, state: &'s S) -> Result<Self::Output, Self::Error>;
}

impl<'s, S, T, A> PureEvaluator<'s, S, T> for A
where
    A: Evaluator<&'s S, T>,
    T: Tree,
    S: 's,
{
    #[inline(always)]
    fn evaluate_pure(tree: T, state: &'s S) -> Result<Self::Output, Self::Error> {
        Self::evaluate(tree, state).map(|(output, _)| output)
    }
}

/// A trait for evaluating trees without contextual state.
pub trait StatelessEvaluator<T>
where
    Self: Evaluator<(), T>,
    T: Tree,
{
    /// Evaluates the given `tree` without contextual state.
    fn evaluate_stateless(tree: T) -> Result<Self::Output, Self::Error>;
}

impl<T, A> StatelessEvaluator<T> for A
where
    A: Evaluator<(), T>,
    T: Tree,
{
    #[inline(always)]
    fn evaluate_stateless(tree: T) -> Result<Self::Output, Self::Error> {
        Self::evaluate(tree, ()).map(|(output, _)| output)
    }
}
