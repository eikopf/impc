//! Well-formed IMP integer semantics.

use std::{fmt::{Display, LowerHex, UpperHex}, ops::{Add, Deref, Mul, Sub}};

use num_traits::{Bounded, ConstOne, ConstZero, One, SaturatingSub, Zero};

/// A `usize` conforming to IMP semantics.
pub type ImpUsize = ImpInt<usize>;
/// A `u8` conforming to IMP semantics.
pub type ImpU8 = ImpInt<u8>;
/// A `u16` conforming to IMP semantics.
pub type ImpU16 = ImpInt<u16>;
/// A `u32` conforming to IMP semantics.
pub type ImpU32 = ImpInt<u32>;
/// A `u64` conforming to IMP semantics.
pub type ImpU64 = ImpInt<u64>;
/// A `u128` conforming to IMP semantics.
pub type ImpU128 = ImpInt<u128>;

/// A thin wrapper around an unsigned integer of type `T`, modifying
/// its [`Sub`] implementation to conform to IMP's integer semantics.
///
/// # Guarantees
/// - `ImpInt<T>` has the same memory layout and size as `T`;
/// - `ImpInt<T>` implements [`Add`] and [`Mul`] by transparently deferring to the corresponding
///    implementations on `T`;
/// - The [`Sub`] implementation on `ImpInt<T>` defers to a transparent invocation of [`SaturatingSub`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct ImpInt<T>(T);

impl<T> From<T> for ImpInt<T>  {
    #[inline(always)]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> Deref for ImpInt<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Display> Display for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Display>::fmt(&self.0, f)
    }
}

impl<T: LowerHex> LowerHex for ImpInt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as LowerHex>::fmt(&self.0, f)
    }
}

impl<T: UpperHex> UpperHex for ImpInt<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as UpperHex>::fmt(&self.0, f)
    }
}

impl<T: Zero> Zero for ImpInt<T> {
    #[inline(always)]
    fn zero() -> Self {
        Self(T::zero())
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        T::is_zero(&self.0)
    }
}

impl<T: ConstZero> ConstZero for ImpInt<T> {
    const ZERO: Self = Self(T::ZERO);
}

impl<T: One> One for ImpInt<T> {
    #[inline(always)]
    fn one() -> Self {
        Self(T::one())
    }
}

impl<T: ConstOne> ConstOne for ImpInt<T> {
    const ONE: Self = Self(T::ONE);
}

impl<T: Bounded> Bounded for ImpInt<T> {
    #[inline(always)]
    fn min_value() -> Self {
        Self(T::min_value())
    }

    #[inline(always)]
    fn max_value() -> Self {
        Self(T::max_value())
    }
}

impl<T: Add<Output = T>> Add for ImpInt<T> {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl<T: Mul<Output = T>> Mul for ImpInt<T> {
    type Output = Self;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl<T: SaturatingSub<Output = T>> Sub for ImpInt<T> {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0.saturating_sub(&rhs.0))
    }
}

impl<T> ImpInt<T> {
    /// Consumes `self` and returns the underlying value.
    #[inline(always)]
    pub fn get(self) -> T {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sub_impl_is_saturating() {
        let lhs = ImpInt::<usize>(10);
        let rhs = ImpInt::<usize>(12);
        assert_eq!(ImpUsize::ZERO, lhs - rhs);
    }
}
