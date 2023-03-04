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
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate_hash<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => N::hash_bhp256(&input.to_bits_le())?,
            1 => N::hash_bhp512(&input.to_bits_le())?,
            2 => N::hash_bhp768(&input.to_bits_le())?,
            3 => N::hash_bhp1024(&input.to_bits_le())?,
            4 => N::hash_ped64(&input.to_bits_le())?,
            5 => N::hash_ped128(&input.to_bits_le())?,
            6 => N::hash_psd2(&input.to_fields()?)?,
            7 => N::hash_psd4(&input.to_fields()?)?,
            8 => N::hash_psd8(&input.to_fields()?)?,
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        };
        // Store the output.
        registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(Literal::Field(output))))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute_hash<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        use circuit::{ToBits, ToFields};

        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operand.
        let input = registers.load_circuit(stack, &self.operands[0])?;
        // Hash the input.
        let output = match VARIANT {
            0 => A::hash_bhp256(&input.to_bits_le()),
            1 => A::hash_bhp512(&input.to_bits_le()),
            2 => A::hash_bhp768(&input.to_bits_le()),
            3 => A::hash_bhp1024(&input.to_bits_le()),
            4 => A::hash_ped64(&input.to_bits_le()),
            5 => A::hash_ped128(&input.to_bits_le()),
            6 => A::hash_psd2(&input.to_fields()),
            7 => A::hash_psd4(&input.to_fields()),
            8 => A::hash_psd8(&input.to_fields()),
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output =
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Field(output), Default::default()));
        // Store the output.
        registers.store_circuit(stack, &self.destination, output)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn hash_output_types(
        &self,
        _stack: &Stack<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 1 {
            bail!("Instruction '{}' expects 1 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        match VARIANT {
            0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => {
                Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))])
            }
            _ => bail!("Invalid 'hash' variant: {VARIANT}"),
        }
    }
}
