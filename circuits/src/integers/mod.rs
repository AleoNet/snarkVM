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
    Zero as NumZero,
};
use snarkvm_utilities::{
    cmp::Ordering,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Sub},
};
use std::fmt::{Debug, Display};

// TODO (@pranav) Could do a refactor where we create a generic Integer struct with trait
//  bound PrimitiveInteger and implement Add, Eq, Mul, etc. Functionality specific to a
//  signed or unsigned integer could be implemented with further trait bounds on Integer.
//  While this would reduce duplication, it would allow signed and unsigned integers to
//  "interact" with each other, which seems unsafe.

// TODO (@pranav) Do we need a better name for these?
//  In general, need to consider appropriate naming for this entire module.
/// Trait bound for integer values. Common to both signed and unsigned integers.
pub trait PrimitiveInteger:
    'static + Debug + Display + PrimInt + Bounded + NumZero + NumOne + WrappingAdd + WrappingMul + WrappingNeg + NumCast
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
