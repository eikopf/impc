//! A compiler-frontend [`Var`] type providing borrowed copy-on-write semantics.

use byteyarn::{YarnBox, YarnRef};

/// A valid IMP variable, guaranteed to begin
/// with a latin character and to have a body
/// composed of latin characters, digits,
/// and underscores.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Var<'src>(YarnBox<'src, str>);

impl<'src> std::fmt::Display for Var<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'src> From<&'src str> for Var<'src> {
    fn from(value: &'src str) -> Self {
        Self(YarnBox::from(value))
    }
}

impl<'src> Var<'src> {
    /// Returns a reference to the underlying [`YarnBox`].
    pub fn get(&self) -> YarnRef<'_, str> {
        self.0.as_ref()
    }
}
