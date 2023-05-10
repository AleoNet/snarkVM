// Copyright (C) 2019-2023 Aleo Systems Inc.
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

/// Samples a random value for each literal type.
#[macro_export]
macro_rules! sample_literals {
    ($network:ident, $rng:expr) => {
        [
            console::program::Literal::<$network>::Address(console::types::Address::new(Uniform::rand($rng))),
            console::program::Literal::Boolean(console::types::Boolean::rand($rng)),
            console::program::Literal::Field(console::types::Field::rand($rng)),
            console::program::Literal::Group(console::types::Group::rand($rng)),
            console::program::Literal::I8(console::types::I8::rand($rng)),
            console::program::Literal::I16(console::types::I16::rand($rng)),
            console::program::Literal::I32(console::types::I32::rand($rng)),
            console::program::Literal::I64(console::types::I64::rand($rng)),
            console::program::Literal::I128(console::types::I128::rand($rng)),
            console::program::Literal::U8(console::types::U8::rand($rng)),
            console::program::Literal::U16(console::types::U16::rand($rng)),
            console::program::Literal::U32(console::types::U32::rand($rng)),
            console::program::Literal::U64(console::types::U64::rand($rng)),
            console::program::Literal::U128(console::types::U128::rand($rng)),
            console::program::Literal::Scalar(console::types::Scalar::rand($rng)),
            console::program::Literal::String(console::types::StringType::rand($rng)),
        ]
    };
}

///
/// Creates a benchmark of the given operation for each declared case.
///
/// For each declared case, this macro samples random values and checks that
/// the output of the operator (LHS) matches the output of the operation (RHS).
/// In addition, this macro ensures all combinations of literal types that
/// do **not** match these declared cases fail on evaluation.
///
/// ## Example
/// ```ignore
/// ```text
///     test_execute!(
///         rng,
///         stack,
///         finalize_registers,
///         AddWrapped {
///             (Field, Field) => Field,
///             (Group, Group) => Group,
///             (I8, I8) => I8,
///             (I16, I16) => I16,
///             (I32, I32) => I32,
///             (I64, I64) => I64,
///             (I128, I128) => I128,
///             (U8, U8) => U8,
///             (U16, U16) => U16,
///             (U32, U32) => U32,
///             (U64, U64) => U64,
///             (U128, U128) => U128,
///             (Scalar, Scalar) => Scalar,
///         }
///     );
/// ```
#[macro_export]
macro_rules! test_execute {
    // Case 0: Unary operation.
    ($instruction:ident { $( ($input:ident) [ $args:expr ], )+ }) => {
        $( benchmark_instruction(c, stringify!(<$instruction: _ $input>), stack, registers, $args); )+
    };
    // Case 1: Binary operation.
    ($instruction:ident { $( ($input_a:ident, $input_b:ident) [ $args:expr ], )+ }) => {
        $( benchmark_instruction(c, stringify!(<$instruction: _ $input_a _ $input_b>), stack, registers, $args); )+
    };
    // Case 2: Ternary operation.
    ($instruction:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident) [ $args:expr ], )+ }) => {
        $( benchmark_instruction(c, stringify!(<$instruction: _ $input_a _ $input_b _ $input_c>), stack, registers, $args); )+
    };
}
