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
    pub fn evaluate_commit<A: circuit::Aleo<Network = N>, const VARIANT: u8>(
        &self,
        commit: &CommitInstruction<N, VARIANT>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if commit.operands().len() != 2 {
            bail!(
                "Instruction '{}' expects 2 operands, found {} operands",
                CommitInstruction::<N, VARIANT>::opcode(),
                commit.operands().len()
            )
        }

        // Retrieve the input and randomizer.
        let input = registers.load(self, &commit.operands()[0])?;
        let randomizer = registers.load(self, &commit.operands()[1])?;
        // Retrieve the randomizer.
        let randomizer = match randomizer {
            Value::Plaintext(Plaintext::Literal(Literal::Scalar(randomizer), ..)) => randomizer,
            _ => bail!("Invalid randomizer type for the commit evaluation, expected a scalar"),
        };

        // Commit the input.
        let output = match VARIANT {
            0 => Literal::Field(N::commit_bhp256(&input.to_bits_le(), &randomizer)?),
            1 => Literal::Field(N::commit_bhp512(&input.to_bits_le(), &randomizer)?),
            2 => Literal::Field(N::commit_bhp768(&input.to_bits_le(), &randomizer)?),
            3 => Literal::Field(N::commit_bhp1024(&input.to_bits_le(), &randomizer)?),
            4 => Literal::Group(N::commit_ped64(&input.to_bits_le(), &randomizer)?),
            5 => Literal::Group(N::commit_ped128(&input.to_bits_le(), &randomizer)?),
            _ => bail!("Invalid 'commit' variant: {VARIANT}"),
        };
        // Store the output.
        registers.store(self, &commit.destinations()[0], Value::Plaintext(Plaintext::from(output)))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute_commit<A: circuit::Aleo<Network = N>, const VARIANT: u8>(
        &self,
        commit: &CommitInstruction<N, VARIANT>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        use circuit::ToBits;

        // Ensure the number of operands is correct.
        if commit.operands().len() != 2 {
            bail!(
                "Instruction '{}' expects 2 operands, found {} operands",
                CommitInstruction::<N, VARIANT>::opcode(),
                commit.operands().len()
            )
        }

        // Retrieve the input and randomizer.
        let input = registers.load_circuit(self, &commit.operands()[0])?;
        let randomizer = registers.load_circuit(self, &commit.operands()[1])?;
        // Retrieve the randomizer.
        let randomizer = match randomizer {
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Scalar(randomizer), ..)) => {
                randomizer
            }
            _ => bail!("Invalid randomizer type for the commit execution, expected a scalar"),
        };

        // Commits the input.
        let output = match VARIANT {
            0 => circuit::Literal::Field(A::commit_bhp256(&input.to_bits_le(), &randomizer)),
            1 => circuit::Literal::Field(A::commit_bhp512(&input.to_bits_le(), &randomizer)),
            2 => circuit::Literal::Field(A::commit_bhp768(&input.to_bits_le(), &randomizer)),
            3 => circuit::Literal::Field(A::commit_bhp1024(&input.to_bits_le(), &randomizer)),
            4 => circuit::Literal::Group(A::commit_ped64(&input.to_bits_le(), &randomizer)),
            5 => circuit::Literal::Group(A::commit_ped128(&input.to_bits_le(), &randomizer)),
            _ => bail!("Invalid 'commit' variant: {VARIANT}"),
        };
        // Convert the output to a stack value.
        let output = circuit::Value::Plaintext(circuit::Plaintext::Literal(output, Default::default()));
        // Store the output.
        registers.store_circuit(self, &commit.destinations()[0], output)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn commit_output_types<const VARIANT: u8>(
        &self,
        commit: &CommitInstruction<N, VARIANT>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!(
                "Instruction '{}' expects 2 inputs, found {} inputs",
                CommitInstruction::<N, VARIANT>::opcode(),
                input_types.len()
            )
        }
        // Ensure the number of operands is correct.
        if commit.operands().len() != 2 {
            bail!(
                "Instruction '{}' expects 2 operands, found {} operands",
                CommitInstruction::<N, VARIANT>::opcode(),
                commit.operands().len()
            )
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        match VARIANT {
            0 | 1 | 2 | 3 => Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field))]),
            4 | 5 => Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Group))]),
            _ => bail!("Invalid 'commit' variant: {VARIANT}"),
        }
    }
}
