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

use super::*;

impl<N: Network, const VARIANT: u8> Stack<N> {
    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, assert: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", AssertInstruction::opcode(), input_types.len())
        }
        // Ensure the operands are of the same type.
        if input_types[0] != input_types[1] {
            bail!(
                "Instruction '{}' expects inputs of the same type. Found inputs of type '{}' and '{}'",
                AssertInstruction::opcode(),
                input_types[0],
                input_types[1]
            )
        }
        // Ensure the number of operands is correct.
        if assert.operands().len() != 2 {
            bail!(
                "Instruction '{}' expects 2 operands, found {} operands",
                AssertInstruction::opcode(),
                assert.operands().len()
            )
        }

        match VARIANT {
            0 | 1 => Ok(vec![]),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
    }
}
