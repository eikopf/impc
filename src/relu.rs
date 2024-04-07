//! An implementation of IMP's subtraction semantics.

use num_traits::{SaturatingSub, Unsigned};

/// Computes `min(lhs - rhs, 0)`, i.e. saturating subtraction.
pub fn relu<T>(lhs: &T, rhs: &T) -> T
where
    T: SaturatingSub + Unsigned,
{
    T::saturating_sub(lhs, rhs)
}
