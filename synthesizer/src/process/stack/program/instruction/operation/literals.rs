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
use snarkvm_synthesizer_program::Operation;

impl<N: Network> Stack<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate_literals<
        A: circuit::Aleo<Network = N>,
        O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>,
        const NUM_OPERANDS: usize,
    >(
        &self,
        literals: &Literals<N, O, NUM_OPERANDS>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if literals.operands().len() != NUM_OPERANDS {
            bail!(
                "Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands",
                O::OPCODE,
                literals.operands().len()
            )
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            literals.operands().iter().map(|operand| registers.load_literal(self, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let output = O::evaluate(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_type = RegisterType::Plaintext(PlaintextType::from(output.to_type()));

        // Retrieve the expected output type.
        let expected_types = self.literals_output_types(literals, &input_types)?;
        // Ensure there is exactly one output.
        ensure!(expected_types.len() == 1, "Expected 1 output type, found {}", expected_types.len());
        // Ensure the output type is correct.
        ensure!(expected_types[0] == output_type, "Expected output type '{}', found {output_type}", expected_types[0]);

        // Evaluate the operation and store the output.
        registers.store_literal(self, &literals.destinations()[0], output)
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute_literals<
        A: circuit::Aleo<Network = N>,
        O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>,
        const NUM_OPERANDS: usize,
    >(
        &self,
        literals: &Literals<N, O, NUM_OPERANDS>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if literals.operands().len() != NUM_OPERANDS {
            bail!(
                "Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands",
                O::OPCODE,
                literals.operands().len()
            )
        }

        // Load the operands literals.
        let inputs: Vec<_> =
            literals.operands().iter().map(|operand| registers.load_literal_circuit(self, operand)).try_collect()?;
        // Compute the operands register types.
        let input_types: Vec<_> =
            inputs.iter().map(|input| RegisterType::Plaintext(PlaintextType::from(input.to_type()))).collect();

        // Compute the operation.
        let output = O::execute(&inputs.try_into().map_err(|_| anyhow!("Failed to prepare operands in evaluate"))?)?;
        // Compute the output type.
        let output_type = RegisterType::Plaintext(PlaintextType::from(output.to_type()));

        // Retrieve the expected output type.
        let expected_types = self.literals_output_types(literals, &input_types)?;
        // Ensure there is exactly one output.
        ensure!(expected_types.len() == 1, "Expected 1 output type, found {}", expected_types.len());
        // Ensure the output type is correct.
        ensure!(expected_types[0] == output_type, "Expected output type '{}', found {output_type}", expected_types[0]);

        // Evaluate the operation and store the output.
        registers.store_literal_circuit(self, &literals.destinations()[0], output)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn literals_output_types<O: Operation<N, Literal<N>, LiteralType, NUM_OPERANDS>, const NUM_OPERANDS: usize>(
        &self,
        literals: &Literals<N, O, NUM_OPERANDS>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != NUM_OPERANDS {
            bail!("Instruction '{}' expects {NUM_OPERANDS} inputs, found {} inputs", O::OPCODE, input_types.len())
        }
        // Ensure the number of operands is correct.
        if literals.operands().len() != NUM_OPERANDS {
            bail!(
                "Instruction '{}' expects {NUM_OPERANDS} operands, found {} operands",
                O::OPCODE,
                literals.operands().len()
            )
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
