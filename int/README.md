# `imp_int`
> What is an integer newtype but a miserable pile of macros?

This crate provides the following thinly-wrapped types:
- `u8 => Imp8`;
- `u16 => Imp16`;
- `u32 => Imp32`;
- `u64 => Imp64`;
- `u128 => Imp128`;
- `usize => ImpSize`.

With the `bigint` feature enabled, it also provides the `ImpBigInt` type as a wrapper over the [`num_bigint::BigUint`](https://docs.rs/num-bigint/latest/num_bigint/struct.BigUint.html) type to provide an arbitrary precision integer with IMP integer semantics.

## Installation
```sh
# ordinary usage
cargo add imp_int

# usage with the bigint feature enabled
cargo add imp_int --features bigint
```
