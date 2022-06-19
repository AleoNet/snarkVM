// Copyright (C) 2019-2022 Aleo Systems Inc.
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

mod call;
pub use call::*;

mod cast;
pub use cast::*;

mod literals;
pub use literals::*;

mod macros;

use crate::vm::Opcode;
use console::network::prelude::*;

pub trait Operation<N: Network, Value: Parser + ToBits, CircuitValue, ValueType: Parser, const NUM_OPERANDS: usize> {
    /// The opcode of the operation.
    const OPCODE: Opcode;

    /// Returns the result of evaluating the operation on the given inputs.
    fn evaluate(inputs: &[Value; NUM_OPERANDS]) -> Result<Value>;

    /// Returns the result of executing the operation on the given circuit inputs.
    fn execute(inputs: &[CircuitValue; NUM_OPERANDS]) -> Result<CircuitValue>;

    /// Returns the output type from the given input types.
    fn output_type(inputs: &[ValueType; NUM_OPERANDS]) -> Result<ValueType>;
}

/// Adds `first` with `second`, storing the outcome in `destination`.
pub type Add<N, A> = BinaryLiteral<N, A, AddOperation<N, A>>;

crate::operation!(
    pub struct AddOperation<core::ops::Add, add, "add"> {
        (Field, Field) => Field,
        (Group, Group) => Group,
        (I8, I8) => I8 ("ensure overflows halt"),
        (I16, I16) => I16 ("ensure overflows halt"),
        (I32, I32) => I32 ("ensure overflows halt"),
        (I64, I64) => I64 ("ensure overflows halt"),
        (I128, I128) => I128 ("ensure overflows halt"),
        (U8, U8) => U8 ("ensure overflows halt"),
        (U16, U16) => U16 ("ensure overflows halt"),
        (U32, U32) => U32 ("ensure overflows halt"),
        (U64, U64) => U64 ("ensure overflows halt"),
        (U128, U128) => U128 ("ensure overflows halt"),
        (Scalar, Scalar) => Scalar,
    }
);

/// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
pub type AddWrapped<N, A> = BinaryLiteral<N, A, AddWrappedOperation<N, A>>;

crate::operation!(
    pub struct AddWrappedOperation<console::network::AddWrapped, add_wrapped, "add.w"> {
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);

/// Performs a bitwise `and` on `first` and `second`, storing the outcome in `destination`.
pub type And<N, A> = BinaryLiteral<N, A, AndOperation<N, A>>;

crate::operation!(
    pub struct AndOperation<core::ops::BitAnd, bitand, "and"> {
        (Boolean, Boolean) => Boolean,
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);

// /// Divides `first` by `second`, storing the outcome in `destination`.
// pub type Div<N, A> = BinaryLiteral<N, A, DivOperation<N, A>>;
//
// crate::operation!(
//     pub struct DivOperation<core::ops::Div, div, "div"> {
//         (Field, Field) => Field,
//         (I8, I8) => I8 ("ensure overflows halt", "ensure divide by zero halts"),
//         (I16, I16) => I16 ("ensure overflows halt", "ensure divide by zero halts"),
//         (I32, I32) => I32 ("ensure overflows halt", "ensure divide by zero halts"),
//         (I64, I64) => I64 ("ensure overflows halt", "ensure divide by zero halts"),
//         (I128, I128) => I128 ("ensure overflows halt", "ensure divide by zero halts"),
//         (U8, U8) => U8 ("ensure overflows halt", "ensure divide by zero halts"),
//         (U16, U16) => U16 ("ensure overflows halt", "ensure divide by zero halts"),
//         (U32, U32) => U32 ("ensure overflows halt", "ensure divide by zero halts"),
//         (U64, U64) => U64 ("ensure overflows halt", "ensure divide by zero halts"),
//         (U128, U128) => U128 ("ensure overflows halt", "ensure divide by zero halts"),
//         (Scalar, Scalar) => Scalar,
//     }
// );

// /// Divides `first` by `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
// pub type DivWrapped<N, A> = BinaryLiteral<N, A, DivWrappedOperation<N, A>>;
//
// crate::operation!(
//     pub struct DivWrappedOperation<console::network::DivWrapped, div_wrapped, "div.w"> {
//         (I8, I8) => I8 ("ensure divide by zero halts"),
//         (I16, I16) => I16 ("ensure divide by zero halts"),
//         (I32, I32) => I32 ("ensure divide by zero halts"),
//         (I64, I64) => I64 ("ensure divide by zero halts"),
//         (I128, I128) => I128 ("ensure divide by zero halts"),
//         (U8, U8) => U8 ("ensure divide by zero halts"),
//         (U16, U16) => U16 ("ensure divide by zero halts"),
//         (U32, U32) => U32 ("ensure divide by zero halts"),
//         (U64, U64) => U64 ("ensure divide by zero halts"),
//         (U128, U128) => U128 ("ensure divide by zero halts"),
//     }
// );

/// Multiplies `first` and `second`, storing the outcome in `destination`.
pub type Mul<N, A> = BinaryLiteral<N, A, MulOperation<N, A>>;

crate::operation!(
    pub struct MulOperation<core::ops::Mul, mul, "mul"> {
        (Field, Field) => Field,
        (Group, Scalar) => Group,
        (Scalar, Group) => Group,
        (I8, I8) => I8 ("ensure overflows halt"),
        (I16, I16) => I16 ("ensure overflows halt"),
        (I32, I32) => I32 ("ensure overflows halt"),
        (I64, I64) => I64 ("ensure overflows halt"),
        (I128, I128) => I128 ("ensure overflows halt"),
        (U8, U8) => U8 ("ensure overflows halt"),
        (U16, U16) => U16 ("ensure overflows halt"),
        (U32, U32) => U32 ("ensure overflows halt"),
        (U64, U64) => U64 ("ensure overflows halt"),
        (U128, U128) => U128 ("ensure overflows halt"),
        // (Scalar, Scalar) => Scalar,
    }
);

/// Multiplies `first` and `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub type MulWrapped<N, A> = BinaryLiteral<N, A, MulWrappedOperation<N, A>>;

crate::operation!(
    pub struct MulWrappedOperation<console::network::MulWrapped, mul_wrapped, "mul.w"> {
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);

/// Performs a bitwise `or` on `first` and `second`, storing the outcome in `destination`.
pub type Or<N, A> = BinaryLiteral<N, A, OrOperation<N, A>>;

crate::operation!(
    pub struct OrOperation<core::ops::BitOr, bitor, "or"> {
        (Boolean, Boolean) => Boolean,
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);

/// Raises `first` to the power of `second`, storing the outcome in `destination`.
pub type Pow<N, A> = BinaryLiteral<N, A, PowOperation<N, A>>;

crate::operation!(
    pub struct PowOperation<num_traits::Pow, pow, "pow"> {
        (Field, Field) => Field,
        (I8, U8) => I8 ("ensure exponentiation overflows halt"),
        (I8, U16) => I8 ("ensure exponentiation overflows halt"),
        (I8, U32) => I8 ("ensure exponentiation overflows halt"),
        (I16, U8) => I16 ("ensure exponentiation overflows halt"),
        (I16, U16) => I16 ("ensure exponentiation overflows halt"),
        (I16, U32) => I16 ("ensure exponentiation overflows halt"),
        (I32, U8) => I32 ("ensure exponentiation overflows halt"),
        (I32, U16) => I32 ("ensure exponentiation overflows halt"),
        (I32, U32) => I32 ("ensure exponentiation overflows halt"),
        (I64, U8) => I64 ("ensure exponentiation overflows halt"),
        (I64, U16) => I64 ("ensure exponentiation overflows halt"),
        (I64, U32) => I64 ("ensure exponentiation overflows halt"),
        (I128, U8) => I128 ("ensure exponentiation overflows halt"),
        (I128, U16) => I128 ("ensure exponentiation overflows halt"),
        (I128, U32) => I128 ("ensure exponentiation overflows halt"),
        (U8, U8) => U8 ("ensure exponentiation overflows halt"),
        (U8, U16) => U8 ("ensure exponentiation overflows halt"),
        (U8, U32) => U8 ("ensure exponentiation overflows halt"),
        (U16, U8) => U16 ("ensure exponentiation overflows halt"),
        (U16, U16) => U16 ("ensure exponentiation overflows halt"),
        (U16, U32) => U16 ("ensure exponentiation overflows halt"),
        (U32, U8) => U32 ("ensure exponentiation overflows halt"),
        (U32, U16) => U32 ("ensure exponentiation overflows halt"),
        (U32, U32) => U32 ("ensure exponentiation overflows halt"),
        (U64, U8) => U64 ("ensure exponentiation overflows halt"),
        (U64, U16) => U64 ("ensure exponentiation overflows halt"),
        (U64, U32) => U64 ("ensure exponentiation overflows halt"),
        (U128, U8) => U128 ("ensure exponentiation overflows halt"),
        (U128, U16) => U128 ("ensure exponentiation overflows halt"),
        (U128, U32) => U128 ("ensure exponentiation overflows halt"),
    }
);

/// Raises `first` to the power of `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub type PowWrapped<N, A> = BinaryLiteral<N, A, PowWrappedOperation<N, A>>;

crate::operation!(
    pub struct PowWrappedOperation<console::network::PowWrapped, pow_wrapped, "pow.w"> {
        (I8, U8) => I8,
        (I8, U16) => I8,
        (I8, U32) => I8,
        (I16, U8) => I16,
        (I16, U16) => I16,
        (I16, U32) => I16,
        (I32, U8) => I32,
        (I32, U16) => I32,
        (I32, U32) => I32,
        (I64, U8) => I64,
        (I64, U16) => I64,
        (I64, U32) => I64,
        (I128, U8) => I128,
        (I128, U16) => I128,
        (I128, U32) => I128,
        (U8, U8) => U8,
        (U8, U16) => U8,
        (U8, U32) => U8,
        (U16, U8) => U16,
        (U16, U16) => U16,
        (U16, U32) => U16,
        (U32, U8) => U32,
        (U32, U16) => U32,
        (U32, U32) => U32,
        (U64, U8) => U64,
        (U64, U16) => U64,
        (U64, U32) => U64,
        (U128, U8) => U128,
        (U128, U16) => U128,
        (U128, U32) => U128,
    }
);

/// Computes `first - second`, storing the outcome in `destination`.
pub type Sub<N, A> = BinaryLiteral<N, A, SubOperation<N, A>>;

crate::operation!(
    pub struct SubOperation<core::ops::Sub, sub, "sub"> {
        (Field, Field) => Field,
        (Group, Group) => Group,
        (I8, I8) => I8 ("ensure overflows halt"),
        (I16, I16) => I16 ("ensure overflows halt"),
        (I32, I32) => I32 ("ensure overflows halt"),
        (I64, I64) => I64 ("ensure overflows halt"),
        (I128, I128) => I128 ("ensure overflows halt"),
        (U8, U8) => U8 ("ensure overflows halt"),
        (U16, U16) => U16 ("ensure overflows halt"),
        (U32, U32) => U32 ("ensure overflows halt"),
        (U64, U64) => U64 ("ensure overflows halt"),
        (U128, U128) => U128 ("ensure overflows halt"),
        // (Scalar, Scalar) => Scalar,
    }
);

/// Computes `first - second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
pub type SubWrapped<N, A> = BinaryLiteral<N, A, SubWrappedOperation<N, A>>;

crate::operation!(
    pub struct SubWrappedOperation<console::network::SubWrapped, sub_wrapped, "sub.w"> {
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);

/// Performs a bitwise `xor` on `first` and `second`, storing the outcome in `destination`.
pub type Xor<N, A> = BinaryLiteral<N, A, XorOperation<N, A>>;

crate::operation!(
    pub struct XorOperation<core::ops::BitXor, bitxor, "xor"> {
        (Boolean, Boolean) => Boolean,
        (I8, I8) => I8,
        (I16, I16) => I16,
        (I32, I32) => I32,
        (I64, I64) => I64,
        (I128, I128) => I128,
        (U8, U8) => U8,
        (U16, U16) => U16,
        (U32, U32) => U32,
        (U64, U64) => U64,
        (U128, U128) => U128,
    }
);
