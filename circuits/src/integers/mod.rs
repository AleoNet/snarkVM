// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

pub mod signed;
pub use signed::*;

pub mod unsigned;
pub use unsigned::*;

use num_traits::{
    AsPrimitive,
    Bounded,
    NumCast,
    NumOps,
    One as NumOne,
    Pow,
    PrimInt,
    Signed,
    Unsigned,
    WrappingAdd,
    WrappingMul,
    WrappingNeg,
    WrappingSub,
    Zero as NumZero,
};
use snarkvm_utilities::{
    cmp::Ordering,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Sub},
};
use std::fmt::{Debug, Display};

// TODO (@pranav) Gadget Trait
//  fn is_constant()
//  fn eject()_value()

// TODO (@pranav) Could do a refactor where we create a generic Integer struct with trait
//  bound PrimitiveInteger and implement Add, Eq, Mul, etc. Functionality specific to a
//  signed or unsigned integer could be implemented with further trait bounds on Integer.
//  While this would reduce duplication, it would allow signed and unsigned integers to
//  "interact" with each other, which seems unsafe.

// TODO (@pranav) Do we need a better name for these?
//  In general, need to consider appropriate naming for this entire module.
/// Trait bound for integer values. Common to both signed and unsigned integers.
pub trait PrimitiveInteger:
    'static
    + Debug
    + Display
    + PrimInt
    + Bounded
    + NumZero
    + NumOne
    + WrappingAdd
    + WrappingMul
    + WrappingNeg
    + WrappingSub
    + WrappingDiv
    + NumCast
{
}

/// Trait bound for signed integer values.
pub trait PrimitiveSignedInteger: PrimitiveInteger + Signed {}

/// Trait bound for unsigned integer values.
pub trait PrimitiveUnsignedInteger: PrimitiveInteger + Unsigned {}

// TODO (@pranav) Could have gone with extensive "where" clauses but
//  felt that this was cleaner. Suggestions?
impl PrimitiveInteger for i8 {}
impl PrimitiveInteger for i16 {}
impl PrimitiveInteger for i32 {}
impl PrimitiveInteger for i64 {}
impl PrimitiveInteger for i128 {}
impl PrimitiveSignedInteger for i8 {}
impl PrimitiveSignedInteger for i16 {}
impl PrimitiveSignedInteger for i32 {}
impl PrimitiveSignedInteger for i64 {}
impl PrimitiveSignedInteger for i128 {}

impl PrimitiveInteger for u8 {}
impl PrimitiveInteger for u16 {}
impl PrimitiveInteger for u32 {}
impl PrimitiveInteger for u64 {}
impl PrimitiveInteger for u128 {}
impl PrimitiveUnsignedInteger for u8 {}
impl PrimitiveUnsignedInteger for u16 {}
impl PrimitiveUnsignedInteger for u32 {}
impl PrimitiveUnsignedInteger for u64 {}
impl PrimitiveUnsignedInteger for u128 {}

// TODO (@pranav) Find a better place for this
//   Taken from/extending num_traits
macro_rules! wrapping_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
    ($trait_name:ident, $method:ident, $t:ty, $rhs:ty) => {
        impl $trait_name<$rhs> for $t {
            #[inline]
            fn $method(&self, v: &$rhs) -> Self {
                <$t>::$method(*self, *v)
            }
        }
    };
}

pub trait WrappingDiv: Sized + Div<Self, Output = Self> {
    fn wrapping_div(&self, v: &Self) -> Self;
}

wrapping_impl!(WrappingDiv, wrapping_div, u8);
wrapping_impl!(WrappingDiv, wrapping_div, u16);
wrapping_impl!(WrappingDiv, wrapping_div, u32);
wrapping_impl!(WrappingDiv, wrapping_div, u64);
wrapping_impl!(WrappingDiv, wrapping_div, u128);
wrapping_impl!(WrappingDiv, wrapping_div, i8);
wrapping_impl!(WrappingDiv, wrapping_div, i16);
wrapping_impl!(WrappingDiv, wrapping_div, i32);
wrapping_impl!(WrappingDiv, wrapping_div, i64);
wrapping_impl!(WrappingDiv, wrapping_div, i128);

#[cfg(test)]
pub mod test_utilities {
    use crate::{Boolean, Environment};

    // TODO (@pranav) This helper function can be generalized across test_utilities.
    /// Checks that a given candidate gadget matches the expected result. Optionally checks
    /// that the number of constants, public variables, private variables, and constraints
    /// for the corresponding circuit matches some expected number.
    pub fn check_boolean_operation<E: Environment>(
        name: &str,
        expected: bool,
        compute_candidate: &dyn Fn() -> Boolean<E>,
        circuit_properties: Option<(usize, usize, usize, usize)>,
    ) {
        E::scoped(name, |scope| {
            let candidate = compute_candidate();
            println!(
                "Constant: {:?}, Public: {:?}, Private: {:?}, Constraints: {:?}",
                scope.num_constants_in_scope(),
                scope.num_public_in_scope(),
                scope.num_private_in_scope(),
                scope.num_constraints_in_scope()
            );
            assert_eq!(expected, candidate.eject_value());
            if let Some((num_constants, num_public, num_private, num_constraints)) = circuit_properties {
                assert_eq!(num_constants, scope.num_constants_in_scope());
                assert_eq!(num_public, scope.num_public_in_scope());
                assert_eq!(num_private, scope.num_private_in_scope());
                assert_eq!(num_constraints, scope.num_constraints_in_scope());
            }
            assert!(E::is_satisfied());
        });
    }
}
