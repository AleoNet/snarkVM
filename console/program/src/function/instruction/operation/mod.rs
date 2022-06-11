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

mod binary;
pub(crate) use binary::*;

mod ternary;
pub(crate) use ternary::*;

use crate::LiteralType;
use snarkvm_console_network::prelude::*;

/// Creates a match statement that evaluates the operation.
///
/// ## Example
/// ```ignore
/// evaluate!(
///     match Add::add(first, second) {
///         (I8, I8) => I8,
///         (I16, I16) => I16,
///         (I32, I32) => I32,
///         (I64, I64) => I64,
///         (I128, I128) => I128,
///         (U8, U8) => U8,
///         (U16, U16) => U16,
///         (U32, U32) => U32,
///         (U64, U64) => U64,
///         (U128, U128) => U128,
///     }
/// )
/// ```
#[macro_export]
macro_rules! evaluate {
    // Binary operation.
    (match $operator:tt::$operation:tt($first:expr, $second:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        match ($first, $second) {
            $((Literal::$input_a(first), Literal::$input_b(second)) => Literal::$output($operator::$operation(first, second)),)+
            _ => bail!("Invalid operands for the '{}' instruction", Self::OPCODE),
        }
    }};
}

/// Creates a match statement that returns the output type given the input types.
///
/// ## Example
/// ```ignore
/// output_type!(
///     match (first, second) {
///         (I8, I8) => I8,
///         (I16, I16) => I16,
///         (I32, I32) => I32,
///         (I64, I64) => I64,
///         (I128, I128) => I128,
///         (U8, U8) => U8,
///         (U16, U16) => U16,
///         (U32, U32) => U32,
///         (U64, U64) => U64,
///         (U128, U128) => U128,
///     }
/// )
/// ```
#[macro_export]
macro_rules! output_type {
    // Binary operation.
    (match ($first:expr, $second:expr) { $( ($input_a:ident, $input_b:ident) => $output:ident, )+ }) => {{
        match ($first, $second) {
            $((LiteralType::$input_a, LiteralType::$input_b) => LiteralType::$output,)+
            _ => bail!("Invalid operand types for the '{}' instruction", Self::OPCODE),
        }
    }};
}

pub trait Operation {
    type InputTypes;
    type Inputs;
    type Output;

    /// The opcode of the operation.
    const OPCODE: &'static str;

    /// Returns the result of evaluating the operation on the given inputs.
    fn evaluate(inputs: Self::Inputs) -> Result<Self::Output>;

    /// Returns the output type from the given input types.
    fn output_type(inputs: Self::InputTypes) -> Result<LiteralType>;
}
