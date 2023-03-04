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

impl<N: Network> Stack<N> {
    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, _stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} inputs, found {} inputs", O::OPCODE, input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }

        // Convert all input types into `LiteralType`s. If any are not a `LiteralType`, return an error.
        let input_types = input_types
            .iter()
            .copied()
            .map(|input_type| match input_type {
                RegisterType::Plaintext(PlaintextType::Literal(literal_type)) => Ok(literal_type),
                RegisterType::Plaintext(PlaintextType::Struct(..)) => {
                    bail!("Expected literal type, found '{input_type}'")
                }
                RegisterType::Record(..) => bail!("Expected literal type, found '{input_type}'"),
                RegisterType::ExternalRecord(..) => bail!("Expected literal type, found '{input_type}'"),
            })
            .collect::<Result<Vec<_>>>()?;

        // Compute the output type.
        let output = O::output_type(&input_types.try_into().map_err(|_| anyhow!("Failed to prepare operand types"))?)?;

        // Return the output type.
        Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(output))])
    }
}
