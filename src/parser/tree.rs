//! Traits and functions modelling tree-structure.

/// A trait generalising tree-structure.
pub trait Tree {
    /// The type of the nodes in this tree.
    type Node;

    /// Consumes `self` and maps `op` over it, typically by
    /// applying `op` to its root.
    fn map<U, F>(self, op: F) -> U where F: FnOnce(Self::Node) -> U;
}

/// A SAM trait for types with rooted tree-structure.
pub trait Rooted {
    /// The type of the root node in this tree.
    type RootNode;

    /// Returns a reference to the root of `self`.
    fn root(&self) -> &Self::RootNode;
}
