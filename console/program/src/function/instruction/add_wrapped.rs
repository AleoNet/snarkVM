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

use crate::{
    function::instruction::{BinaryLiteral, Operation},
    Literal,
    LiteralType,
};
use snarkvm_console_network::prelude::*;

use core::marker::PhantomData;

/// The number of operands for the operation.
const NUM_OPERANDS: usize = 2;

/// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
pub type AddWrapped<N> = BinaryLiteral<N, AddWrappedOp<N>>;

pub struct AddWrappedOp<N: Network>(PhantomData<N>);

impl<N: Network> Operation<N, Literal<N>, LiteralType, NUM_OPERANDS> for AddWrappedOp<N> {
    /// The opcode of the operation.
    const OPCODE: &'static str = "add.w";

    /// Returns the result of evaluating the operation on the given inputs.
    #[inline]
    fn evaluate(inputs: &[Literal<N>; NUM_OPERANDS]) -> Result<Literal<N>> {
        // Retrieve the first and second operands.
        let [first, second] = inputs;

        // Prepare the operator.
        use snarkvm_console_network::AddWrapped as Operator;

        // Perform the operation.
        let output = crate::evaluate!(match first.add_wrapped(second) {
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
        });

        // Return the output.
        Ok(output)
    }

    /// Returns the output type from the given input types.
    #[inline]
    fn output_type(inputs: &[LiteralType; NUM_OPERANDS]) -> Result<LiteralType> {
        // Retrieve the first and second operands.
        let [first, second] = inputs;

        // Compute the output type.
        Ok(crate::output_type!(match (first, second) {
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
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Declare the operator to check.
    use snarkvm_console_network::AddWrapped as Operator;

    // Declare the opcode to check.
    use super::AddWrappedOp as Opcode;

    // For each declared case, this macro samples random values and checks that
    // the output of the operator (LHS) matches the output of the opcode (RHS).
    // In addition, this macro ensures all combinations of literal types that
    // do **not** match these declared cases fail on evaluation.
    crate::test_evaluate!(
        Operator::add_wrapped == Opcode::evaluate {
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
}
