//! Well-formed IMP integer semantics.

use std::{
    fmt::{Binary, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex},
    ops::{Add, Deref, Div, Mul, Rem, Sub},
    str::FromStr,
};

use num_bigint::BigUint;
use num_traits::{Bounded, ConstOne, ConstZero, Num, One, SaturatingSub, Unsigned, Zero};

/// A `usize` conforming to IMP semantics.
pub type ImpSize = ImpInt<usize>;
/// A `u8` conforming to IMP semantics.
pub type Imp8 = ImpInt<u8>;
/// A `u16` conforming to IMP semantics.
pub type Imp16 = ImpInt<u16>;
/// A `u32` conforming to IMP semantics.
pub type Imp32 = ImpInt<u32>;
/// A `u64` conforming to IMP semantics.
pub type Imp64 = ImpInt<u64>;
/// A `u128` conforming to IMP semantics.
pub type Imp128 = ImpInt<u128>;
/// An arbitrary-precision unsigned integer conforming
/// to IMP semantics. Its maximum value is architecture
/// dependent, but is guaranteed to be at least `32^(2^31)` 
/// on 32-bit targets and at least `32^(2^63)` on 64-bit
/// targets.
pub type ImpBigInt = ImpInt<BigUint>;

impl Add for ImpBigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Mul for ImpBigInt {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Sub for ImpBigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        // BigUint doesn't implement SaturatingSub, so this
        // manual check is required
        Self(match self.0 > rhs.0 {
            true => self.0 - rhs.0,
            false => BigUint::zero(),
        })
    }
}

/// Creates `impl` blocks with associated constants for the given `ImpInt<$int>` types.
macro_rules! imp_int_impls {
    ($int:ty) => {
        impl ImpInt<$int> {
            /// The minimum value representable by this type, i.e. zero.
            pub const MIN: Self = Self(<$int>::MIN);
            /// The maximum value representable by this type.
            pub const MAX: Self = Self(<$int>::MAX);
        }

        // assertion: INT::MIN == INT::ZERO
        crate::sa::const_assert_eq!(ImpInt::<$int>::MIN.0, <$int>::ZERO);

        impl std::ops::Add for ImpInt<$int> {
            type Output = Self;

            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                Self(self.0.checked_add(rhs.0)
                    .expect("attempted addition which would have caused integer overflow"))
            }
        }

        impl std::ops::Mul for ImpInt<$int> {
            type Output = Self;

            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                Self(self.0.checked_mul(rhs.0)
                    .expect("attempted multiplication which would have caused integer overflow"))
            }
        }

        impl std::ops::Sub for ImpInt<$int> {
            type Output = Self;

            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                Self(self.0.saturating_sub(rhs.0))
            }
        }
    };

    ($head:ty, $($tail:ty),+) => {
        imp_int_impls!($head);
        imp_int_impls!($($tail),+);
    };
}

/// Creates `impl TryFrom<usize>` blocks for the given `ImpInt<$int>` types.
macro_rules! imp_int_try_from_usize {
    ($int:ty) => {
        impl std::convert::TryFrom<usize> for ImpInt<$int> {
            type Error = <$int as TryFrom<usize>>::Error;

            fn try_from(value: usize) -> Result<Self, Self::Error> {
                value.try_into().map(Self)
            }
        }
    };

    ($head:ty, $($tail:ty),+) => {
        imp_int_try_from_usize!($head);
        imp_int_try_from_usize!($($tail),+);
    };
}

imp_int_impls!(usize, u8, u16, u32, u64, u128);
imp_int_try_from_usize!(u8, u16, u32, u64, u128, BigUint);

/// A thin wrapper around an integer of type `T`, modifying
/// its [`Sub`] implementation to conform to IMP's integer semantics.
///
/// # Guarantees
/// - `ImpInt<T>` has the same memory layout and size as `T`;
/// - `ImpInt<T>` implements [`Add`] and [`Mul`] by transparently deferring to the corresponding
///    implementations on `T`;
/// - The [`Sub`] implementation on `ImpInt<T>` defers to a transparent invocation of [`SaturatingSub`].
///
/// # Invalid Operations
/// To implement [`Num`] and [`Unsigned`], a type is required to implement [`Div`] and [`Rem`].
/// These operations are however entirely undefined for IMP integers, and so the corresponding
/// implementations on [`ImpInt`] immediately panic when invoked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct ImpInt<T>(T);

impl<T> From<T> for ImpInt<T> {
    #[inline(always)]
    fn from(value: T) -> Self {
        Self(value)
    }
}

impl<T> Deref for ImpInt<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: FromStr> FromStr for ImpInt<T> {
    type Err = <T as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        T::from_str(s).map(Self)
    }
}

impl<T: Display> Display for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Display>::fmt(&self.0, f)
    }
}

impl<T: Binary> Binary for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Binary>::fmt(&self.0, f)
    }
}

impl<T: Octal> Octal for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Octal>::fmt(&self.0, f)
    }
}

impl<T: LowerHex> LowerHex for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as LowerHex>::fmt(&self.0, f)
    }
}

impl<T: UpperHex> UpperHex for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as UpperHex>::fmt(&self.0, f)
    }
}

impl<T: LowerExp> LowerExp for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as LowerExp>::fmt(&self.0, f)
    }
}

impl<T: UpperExp> UpperExp for ImpInt<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as UpperExp>::fmt(&self.0, f)
    }
}

impl<T: Zero> Zero for ImpInt<T>
where
    Self: Add<Output = Self>,
{
    #[inline(always)]
    fn zero() -> Self {
        Self(T::zero())
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        T::is_zero(&self.0)
    }
}

impl<T: ConstZero> ConstZero for ImpInt<T>
where
    Self: Add<Output = Self>,
{
    const ZERO: Self = Self(T::ZERO);
}

impl<T: One> One for ImpInt<T>
where
    Self: Mul<Output = Self>,
{
    #[inline(always)]
    fn one() -> Self {
        Self(T::one())
    }
}

impl<T: ConstOne> ConstOne for ImpInt<T>
where
    Self: Mul<Output = Self>,
{
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

impl<T> Div for ImpInt<T> {
    type Output = Self;

    /// Division is undefined for IMP integers, and this
    /// operation will immediately panic when invoked.
    fn div(self, _rhs: Self) -> Self::Output {
        panic!("Division is an invalid operation for IMP integers.")
    }
}

impl<T> Rem for ImpInt<T> {
    type Output = Self;

    /// Modularity is undefined for IMP integers, and this
    /// operation will immediately panic when invoked.
    fn rem(self, _rhs: Self) -> Self::Output {
        panic!("The modulo operation is undefined for IMP integers")
    }
}

impl<T: Num + SaturatingSub> Num for ImpInt<T>
where
    Self: Add<Output = Self> + Mul<Output = Self> + Sub<Output = Self>,
{
    type FromStrRadixErr = <T as Num>::FromStrRadixErr;

    #[inline(always)]
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        <T as Num>::from_str_radix(str, radix).map(ImpInt)
    }
}

impl<T: Num + Unsigned + SaturatingSub> Unsigned for ImpInt<T> where
    Self: Add<Output = Self> + Mul<Output = Self> + Sub<Output = Self>
{
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
        assert_eq!(ImpSize::ZERO, lhs - rhs);
    }
}
