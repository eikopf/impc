//! Thinly-wrapped integer types modelling IMP integer semantics.
//!
//! In a general sense, an IMP integer is just an unsigned integer with addition and multiplication
//! defined in the normal sense, and where subtraction is defined to saturate at 0. However, this
//! is complicated by the fact that IMP does not define integer overflow; it forces implementations
//! to decide _how_ correct they wish to be.
//!
//! For this reason, the types in this crate implement _checked_ addition and multiplication in
//! both debug and release builds (excluding `ImpBigInt`, which avoids these checks by being
//! practically unbounded).

#![feature(doc_cfg)]

#[cfg(feature = "bigint")]
use num_bigint::BigUint;

/// A `u8` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Imp8(u8);
/// A `u16` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Imp16(u16);
/// A `u32` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Imp32(u32);
/// A `u64` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Imp64(u64);
/// A `u128` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Imp128(u128);
/// A `usize` with IMP integer semantics.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct ImpSize(usize);
/// An arbitrary-precision integer with IMP integer semantics.
#[cfg(feature = "bigint")]
#[doc(cfg(feature = "bigint"))]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct ImpBigInt(BigUint);

#[cfg(feature = "bigint")]
macro_rules! imp_bigint_conversion_impls {
    ($($int:ty => $prim:ty),+) => {
        $(
            #[doc(cfg(feature = "bigint"))]
            impl std::convert::From<$int> for ImpBigInt {
                fn from(value: $int) -> Self {
                    Self(value.0.into())
                }
            }

            #[doc(cfg(feature = "bigint"))]
            impl std::convert::TryFrom<ImpBigInt> for $int {
                type Error = <$prim as std::convert::TryFrom<BigUint>>::Error;

                fn try_from(value: ImpBigInt) -> Result<Self, Self::Error> {
                    value.try_into().map(Self)
                }
            }
        )+
    };
}

/// Generates `From` impls for a `$target` type and the listed primitive `$source` types.
macro_rules! from_impls {
    ($target:ty => { $( $source:ty ),+ }) => {
        $(
            impl std::convert::From<$source> for $target {
                fn from(value: $source) -> Self {
                    Self(value.into())
                }
            }
        )+
    };
}

/// Generates `TryFrom` impls for a `$target` type and the listed primitive `$source` types,
/// with the underlying primitive type given in a `where $int` clause after the `$target`.
macro_rules! try_from_impls {
    ($target:ty where $int:ty => { $( $source:ty ),+ }) => {
        $(
            impl std::convert::TryFrom<$source> for $target {
                type Error = <$int as std::convert::TryFrom<$source>>::Error;

                fn try_from(value: $source) -> Result<Self, Self::Error> {
                    <$int>::try_from(value).map(Self)
                }
            }
        )+
    };
}

/// Generates `From` impls for a `$source` type and the listed primitive `$target` types.
macro_rules! into_prim_impls {
    ($source:ty => { $( $target:ty ),+ }) => {
        $(
            impl std::convert::From<$source> for $target {
                fn from(value: $source) -> Self {
                    value.0.into()
                }
            }
        )+
    };
}

/// Generates `TryFrom` impls for a `$source` type and the listed primitive `$target` types,
/// with the underlying primitive type given in a `where $int` clause after the `$source`.
macro_rules! try_into_prim_impls {
    ($source:ty where $int:ty => { $( $target:ty ),+ }) => {
        $(
            impl std::convert::TryFrom<$source> for $target {
                type Error = <$target as std::convert::TryFrom<$int>>::Error;

                fn try_from(value: $source) -> Result<Self, Self::Error> {
                    value.0.try_into()
                }
            }
        )+
    };
}

/// Generates checked impls for `Add`, `Mul`, and `Sub`.
macro_rules! imp_checked_op_impls {
    ($int:ty => $name:ty) => {
        impl std::ops::Add for $name {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                self.0
                    .checked_add(rhs.0)
                    .map(Self)
                    .expect("attempted addition which would have caused integer overflow")
            }
        }

        impl std::ops::Mul for $name {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                self.0
                    .checked_mul(rhs.0)
                    .map(Self)
                    .expect("attempted multiplication which would have caused integer overflow")
            }
        }

        impl std::ops::Sub for $name {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self {
                Self(self.0.saturating_sub(rhs.0))
            }
        }
    };

    ($($int:ty => $name:ty),+) => {
        $(
            imp_checked_op_impls!($int => $name);
        )+
    };
}

/// Generates the bulk of the impls for the types in this crate.
macro_rules! imp_int_impls {
    ($int:ty => $name:ty) => {
        impl std::fmt::Debug for $name  {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Debug>::fmt(&self.0, f)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::Binary for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::Octal for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::LowerHex for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::UpperHex for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::LowerExp for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl std::fmt::UpperExp for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
                <$int as std::fmt::Display>::fmt(&self.0, f)
            }
        }

        impl num_traits::Zero for $name {
            fn zero() -> Self {
                Self(<$int>::zero())
            }

            fn is_zero(&self) -> bool {
                self.0.is_zero()
            }
        }

        impl num_traits::One for $name {
            fn one() -> Self {
                Self(<$int>::one())
            }
        }

        impl std::str::FromStr for $name {
            type Err = <$int as std::str::FromStr>::Err;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <$int as std::str::FromStr>::from_str(s).map(Self)
            }
        }
    };

    ($($int:ty => $name:ty),+) => {
        $(
            imp_int_impls!($int => $name);
        )+
    };

}

// boilerplate to add conversions between ImpBigInt and the other Imp* types
#[cfg(feature = "bigint")]
imp_bigint_conversion_impls!(
    Imp8 => u8,
    Imp16 => u16,
    Imp32 => u32,
    Imp64 => u64,
    Imp128 => u128,
    ImpSize => usize
);

// FROM IMPLS

// total mapping from arbitrary types to imp integers
from_impls!(Imp8 => { u8 });
from_impls!(Imp16 => { u8, u16, Imp8 });
from_impls!(Imp32 => { u8, u16, u32, Imp8, Imp16 });
from_impls!(Imp64 => { u8, u16, u32, u64, Imp8, Imp16, Imp32 });
from_impls!(Imp128 => { u8, u16, u32, u64, u128, Imp8, Imp16, Imp32, Imp64 });
from_impls!(ImpSize => { u8, u16, usize, Imp8, Imp16 });
#[cfg(feature = "bigint")]
from_impls!(ImpBigInt => { u8, u16, u32, u64, u128, usize });

// total mapping from imp integers to primitive types
into_prim_impls!(Imp8 => { u8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize });
into_prim_impls!(Imp16 => { u16, u32, i32, u64, i64, u128, i128, usize });
into_prim_impls!(Imp32 => { u32, u64, i64, u128, i128 });
into_prim_impls!(Imp64 => { u64, u128, i128 });
into_prim_impls!(Imp128 => { u128 });
into_prim_impls!(ImpSize => { usize });

// TRY_FROM IMPLS

// partial mapping from arbitrary types to imp integers
try_from_impls!(Imp8 where u8 => {
    i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize, Imp16, Imp32, Imp64, Imp128, ImpSize
});
try_from_impls!(Imp16 where u16 => {
    i8, i16, u32, i32, u64, i64, u128, i128, usize, isize, Imp32, Imp64, Imp128, ImpSize
});
try_from_impls!(Imp32 where u32 => {
    i8, i16, i32, u64, i64, u128, i128, usize, isize, Imp64, Imp128, ImpSize
});
try_from_impls!(Imp64 where u64 => {
    i8, i16, i32, i64, u128, i128, usize, isize, Imp128, ImpSize
});
try_from_impls!(Imp128 where u128 => { i8, i16, i32, i64, i128, usize, isize, ImpSize });
try_from_impls!(ImpSize where usize => {
    i8, i16, u32, i32, u64, i64, u128, i128, isize, Imp32, Imp64, Imp128
});
#[cfg(feature = "bigint")]
try_from_impls!(ImpBigInt where BigUint => { i8, i16, i32, i64, i128, isize });

// partial mapping from imp integers to primitive integers
try_into_prim_impls!(Imp8 where u8 => { i8 });
try_into_prim_impls!(Imp16 where u16 => { u8, i8, i16 });
try_into_prim_impls!(Imp32 where u32 => { u8, i8, u16, i16, i32, usize, isize });
try_into_prim_impls!(Imp64 where u64 => { u8, i8, u16, i16, u32, i32, i64, usize, isize });
try_into_prim_impls!(Imp128 where u128 => { u8, i8, u16, i16, u32, i32, u64, i64, i128, usize, isize });
try_into_prim_impls!(ImpSize where usize => { u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, isize });
#[cfg(feature = "bigint")]
try_into_prim_impls!(ImpBigInt where BigUint => {
    u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize
});

imp_checked_op_impls!(
    u8 => Imp8,
    u16 => Imp16,
    u32 => Imp32,
    u64 => Imp64,
    u128 => Imp128,
    usize => ImpSize
);

imp_int_impls!(
    u8 => Imp8,
    u16 => Imp16,
    u32 => Imp32,
    u64 => Imp64,
    u128 => Imp128,
    usize => ImpSize
);

#[cfg(feature = "bigint")]
imp_int_impls!(BigUint => ImpBigInt);

#[cfg(feature = "bigint")]
#[doc(cfg(feature = "bigint"))]
impl std::ops::Add for ImpBigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

#[cfg(feature = "bigint")]
#[doc(cfg(feature = "bigint"))]
impl std::ops::Mul for ImpBigInt {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

#[cfg(feature = "bigint")]
#[doc(cfg(feature = "bigint"))]
impl std::ops::Sub for ImpBigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match self > rhs {
            true => Self(self.0 - rhs.0),
            false => num_traits::Zero::zero(),
        }
    }
}
