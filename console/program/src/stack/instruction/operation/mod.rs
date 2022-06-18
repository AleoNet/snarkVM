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
pub(crate) use call::*;

mod cast;
pub(crate) use cast::*;

mod literal_operation;
pub(crate) use literal_operation::*;

mod macros;

use crate::Opcode;
use snarkvm_console_network::prelude::*;

pub trait Operation<N: Network, Value: Parser + ToBits, ValueType: Parser, const NUM_OPERANDS: usize> {
    /// The opcode of the operation.
    const OPCODE: Opcode;

    /// Returns the result of evaluating the operation on the given inputs.
    fn evaluate(inputs: &[Value; NUM_OPERANDS]) -> Result<Value>;

    /// Returns the output type from the given input types.
    fn output_type(inputs: &[ValueType; NUM_OPERANDS]) -> Result<ValueType>;
}

/// Adds `first` with `second`, storing the outcome in `destination`.
pub type Add<N> = BinaryLiteral<N, AddOperation<N>>;

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
pub type AddWrapped<N> = BinaryLiteral<N, AddWrappedOperation<N>>;

crate::operation!(
    pub struct AddWrappedOperation<snarkvm_console_network::AddWrapped, add_wrapped, "add.w"> {
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

/// Divides `first` by `second`, storing the outcome in `destination`.
pub type Div<N> = BinaryLiteral<N, DivOperation<N>>;

crate::operation!(
    pub struct DivOperation<core::ops::Div, div, "div"> {
        (Field, Field) => Field,
        (I8, I8) => I8 ("ensure overflows halt", "ensure divide by zero halts"),
        (I16, I16) => I16 ("ensure overflows halt", "ensure divide by zero halts"),
        (I32, I32) => I32 ("ensure overflows halt", "ensure divide by zero halts"),
        (I64, I64) => I64 ("ensure overflows halt", "ensure divide by zero halts"),
        (I128, I128) => I128 ("ensure overflows halt", "ensure divide by zero halts"),
        (U8, U8) => U8 ("ensure overflows halt", "ensure divide by zero halts"),
        (U16, U16) => U16 ("ensure overflows halt", "ensure divide by zero halts"),
        (U32, U32) => U32 ("ensure overflows halt", "ensure divide by zero halts"),
        (U64, U64) => U64 ("ensure overflows halt", "ensure divide by zero halts"),
        (U128, U128) => U128 ("ensure overflows halt", "ensure divide by zero halts"),
        (Scalar, Scalar) => Scalar,
    }
);

/// Divides `first` by `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub type DivWrapped<N> = BinaryLiteral<N, DivWrappedOperation<N>>;

crate::operation!(
    pub struct DivWrappedOperation<snarkvm_console_network::DivWrapped, div_wrapped, "div.w"> {
        (I8, I8) => I8 ("ensure divide by zero halts"),
        (I16, I16) => I16 ("ensure divide by zero halts"),
        (I32, I32) => I32 ("ensure divide by zero halts"),
        (I64, I64) => I64 ("ensure divide by zero halts"),
        (I128, I128) => I128 ("ensure divide by zero halts"),
        (U8, U8) => U8 ("ensure divide by zero halts"),
        (U16, U16) => U16 ("ensure divide by zero halts"),
        (U32, U32) => U32 ("ensure divide by zero halts"),
        (U64, U64) => U64 ("ensure divide by zero halts"),
        (U128, U128) => U128 ("ensure divide by zero halts"),
    }
);

/// Multiplies `first` and `second`, storing the outcome in `destination`.
pub type Mul<N> = BinaryLiteral<N, MulOperation<N>>;

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
        (Scalar, Scalar) => Scalar,
    }
);

/// Multiplies `first` and `second`, wrapping around at the boundary of the type, storing the outcome in `destination`.
pub type MulWrapped<N> = BinaryLiteral<N, MulWrappedOperation<N>>;

crate::operation!(
    pub struct MulWrappedOperation<snarkvm_console_network::MulWrapped, mul_wrapped, "mul.w"> {
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

/// Computes `first - second`, storing the outcome in `destination`.
pub type Sub<N> = BinaryLiteral<N, SubOperation<N>>;

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
        (Scalar, Scalar) => Scalar,
    }
);

/// Computes `first - second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
pub type SubWrapped<N> = BinaryLiteral<N, SubWrappedOperation<N>>;

crate::operation!(
    pub struct SubWrappedOperation<snarkvm_console_network::SubWrapped, sub_wrapped, "sub.w"> {
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
