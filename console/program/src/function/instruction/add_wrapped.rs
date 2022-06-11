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
    function::instruction::{Binary, Operation},
    Literal,
    LiteralType,
    Plaintext,
};
use snarkvm_console_network::prelude::*;

use core::marker::PhantomData;

/// Adds `first` with `second`, wrapping around at the boundary of the type, and storing the outcome in `destination`.
pub type AddWrapped<N> = Binary<N, AddWrappedOp<N>>;

pub struct AddWrappedOp<N: Network>(PhantomData<N>);

impl<N: Network> Operation for AddWrappedOp<N> {
    type InputTypes = (LiteralType, LiteralType);
    type Inputs = (Plaintext<N>, Plaintext<N>);
    type Output = Plaintext<N>;

    /// The opcode of the operation.
    const OPCODE: &'static str = "add.w";

    /// Returns the result of evaluating the operation on the given inputs.
    #[inline]
    fn evaluate((first, second): Self::Inputs) -> Result<Self::Output> {
        // Load the first literal.
        let first = match first {
            Plaintext::Literal(literal, ..) => literal,
            _ => bail!("Instruction '{}' expects a literal in the first operand.", Self::OPCODE),
        };

        // Load the second literal.
        let second = match second {
            Plaintext::Literal(literal, ..) => literal,
            _ => bail!("Instruction '{}' expects a literal in the second operand.", Self::OPCODE),
        };

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
        Ok(Plaintext::from(output))
    }

    /// Returns the output type from the given input types.
    #[inline]
    fn output_type((first, second): Self::InputTypes) -> Result<LiteralType> {
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
