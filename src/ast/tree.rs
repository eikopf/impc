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
pub trait NodeCount<T>
where
    Self: Tree,
{
    /// Returns the number of nodes in `self`.
    fn count_nodes(&self) -> T;
}

/// A SAM trait for evaluating trees.
pub trait Evaluator<T> {
    /// The return type of the [`Evaluator::eval`] method.
    type Output;

    /// Returns an evaluation of the given `tree` based on `self`.
    fn eval(self, tree: T) -> Self::Output;
}
