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
    pub fn evaluate_literals<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_literal(stack, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let output = O::evaluate(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_type = RegisterType::Plaintext(PlaintextType::from(output.to_type()));

        // Retrieve the expected output type.
        let expected_types = self.output_types(stack, &input_types)?;
        // Ensure there is exactly one output.
        ensure!(expected_types.len() == 1, "Expected 1 output type, found {}", expected_types.len());
        // Ensure the output type is correct.
        ensure!(expected_types[0] == output_type, "Expected output type '{}', found {output_type}", expected_types[0]);

        // Evaluate the operation and store the output.
        registers.store_literal(stack, &self.destination, output)
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute_literals<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands", O::OPCODE, self.operands.len())
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_literal_circuit(stack, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let output = O::execute(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_type = RegisterType::Plaintext(PlaintextType::from(output.to_type()));

        // Retrieve the expected output type.
        let expected_types = self.output_types(stack, &input_types)?;
        // Ensure there is exactly one output.
        ensure!(expected_types.len() == 1, "Expected 1 output type, found {}", expected_types.len());
        // Ensure the output type is correct.
        ensure!(expected_types[0] == output_type, "Expected output type '{}', found {output_type}", expected_types[0]);

        // Evaluate the operation and store the output.
        registers.store_literal_circuit(stack, &self.destination, output)
    }
}
