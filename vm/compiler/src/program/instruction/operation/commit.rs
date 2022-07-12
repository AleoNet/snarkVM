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

use crate::{Opcode, Operand, Stack};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

use core::marker::PhantomData;

pub trait CommitOperation<N: Network> {
    /// The opcode of the operation.
    const OPCODE: Opcode;

    /// Returns the result of committing to the given input and randomizer.
    fn evaluate(input: Value<N>, randomizer: Value<N>) -> Result<Value<N>>;

    /// Returns the result of committing to the given circuit input and randomizer.
    fn execute<A: circuit::Aleo<Network = N>>(
        input: circuit::Value<A>,
        randomizer: circuit::Value<A>,
    ) -> Result<circuit::Value<A>>;

    /// Returns the output type from the given input types.
    fn output_type() -> Result<RegisterType<N>>;
}

/// BHP256 is a collision-resistant function that processes inputs in 256-bit chunks.
pub type CommitBHP256<N> = CommitInstruction<N, BHPCommitOperation<N, 256>>;
/// BHP512 is a collision-resistant function that processes inputs in 512-bit chunks.
pub type CommitBHP512<N> = CommitInstruction<N, BHPCommitOperation<N, 512>>;
/// BHP768 is a collision-resistant function that processes inputs in 768-bit chunks.
pub type CommitBHP768<N> = CommitInstruction<N, BHPCommitOperation<N, 768>>;
/// BHP1024 is a collision-resistant function that processes inputs in 1024-bit chunks.
pub type CommitBHP1024<N> = CommitInstruction<N, BHPCommitOperation<N, 1024>>;

/// The BHP commitment operation template.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BHPCommitOperation<N: Network, const NUM_BITS: u16>(PhantomData<N>);

impl<N: Network, const NUM_BITS: u16> CommitOperation<N> for BHPCommitOperation<N, NUM_BITS> {
    /// The opcode of the operation.
    const OPCODE: Opcode = match NUM_BITS {
        256 => Opcode::Commit("commit.bhp256"),
        512 => Opcode::Commit("commit.bhp512"),
        768 => Opcode::Commit("commit.bhp768"),
        1024 => Opcode::Commit("commit.bhp1024"),
        _ => panic!("Invalid BHP commit instruction opcode"),
    };

    /// Returns the result of committing to the given input and randomizer.
    fn evaluate(input: Value<N>, randomizer: Value<N>) -> Result<Value<N>> {
        // Retrieve the randomizer.
        let randomizer = match randomizer {
            Value::Plaintext(Plaintext::Literal(Literal::Scalar(randomizer), ..)) => randomizer,
            _ => bail!("Invalid randomizer type for BHP commit"),
        };
        // Compute the commitment.
        let output = match NUM_BITS {
            256 => N::commit_bhp256(&input.to_bits_le(), &randomizer)?,
            512 => N::commit_bhp512(&input.to_bits_le(), &randomizer)?,
            768 => N::commit_bhp768(&input.to_bits_le(), &randomizer)?,
            1024 => N::commit_bhp1024(&input.to_bits_le(), &randomizer)?,
            _ => bail!("Invalid BHP commitment variant: BHP{}", NUM_BITS),
        };
        // Return the output as a stack value.
        Ok(Value::Plaintext(Plaintext::Literal(Literal::Field(output), Default::default())))
    }

    /// Returns the result of committing to the given circuit input and randomizer.
    fn execute<A: circuit::Aleo<Network = N>>(
        input: circuit::Value<A>,
        randomizer: circuit::Value<A>,
    ) -> Result<circuit::Value<A>> {
        use circuit::ToBits;

        // Retrieve the randomizer.
        let randomizer = match randomizer {
            circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Scalar(randomizer), ..)) => {
                randomizer
            }
            _ => bail!("Invalid randomizer type for BHP commit"),
        };
        // Compute the commitment.
        let output = match NUM_BITS {
            256 => A::commit_bhp256(&input.to_bits_le(), &randomizer),
            512 => A::commit_bhp512(&input.to_bits_le(), &randomizer),
            768 => A::commit_bhp768(&input.to_bits_le(), &randomizer),
            1024 => A::commit_bhp1024(&input.to_bits_le(), &randomizer),
            _ => bail!("Invalid BHP commitment variant: BHP{}", NUM_BITS),
        };
        // Return the output as a stack value.
        Ok(circuit::Value::Plaintext(circuit::Plaintext::Literal(circuit::Literal::Field(output), Default::default())))
    }

    /// Returns the output type from the given input types.
    fn output_type() -> Result<RegisterType<N>> {
        Ok(RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field)))
    }
}

/// Commits the operand into the declared type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CommitInstruction<N: Network, O: CommitOperation<N>> {
    /// The operands as `(input, randomizer)`.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// PhantomData.
    _phantom: PhantomData<O>,
}

impl<N: Network, O: CommitOperation<N>> CommitInstruction<N, O> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        O::OPCODE
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Commit operations must have two operands");
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network, O: CommitOperation<N>> CommitInstruction<N, O> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| stack.load(operand)).try_collect()?;
        // Retrieve the input and randomizer.
        let (input, randomizer) = (inputs[0].clone(), inputs[1].clone());
        // Compute the commitment.
        let commitment = O::evaluate(input, randomizer)?;
        // Store the commitment.
        stack.store(&self.destination, commitment)
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N, BaseField = N::Field>>(&self, stack: &mut Stack<N, A>) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }
        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| stack.load_circuit(operand)).try_collect()?;
        // Retrieve the input and randomizer.
        let (input, randomizer) = (inputs[0].clone(), inputs[1].clone());
        // Compute the commitment.
        let commitment = O::execute(input, randomizer)?;
        // Store the commitment.
        stack.store_circuit(&self.destination, commitment)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types<A: circuit::Aleo<Network = N>>(
        &self,
        _stack: &Stack<N, A>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // TODO (howardwu): If the operation is Pedersen, check that it is within the number of bits.

        Ok(vec![O::output_type()?])
    }
}

impl<N: Network, O: CommitOperation<N>> Parser for CommitInstruction<N, O> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        Ok((string, Self { operands: vec![first, second], destination, _phantom: PhantomData }))
    }
}

impl<N: Network, O: CommitOperation<N>> FromStr for CommitInstruction<N, O> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network, O: CommitOperation<N>> Debug for CommitInstruction<N, O> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, O: CommitOperation<N>> Display for CommitInstruction<N, O> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            eprintln!("The number of operands must be 2, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{} ", operand))?;
        write!(f, "into {}", self.destination)
    }
}

impl<N: Network, O: CommitOperation<N>> FromBytes for CommitInstruction<N, O> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination, _phantom: PhantomData })
    }
}

impl<N: Network, O: CommitOperation<N>> ToBytes for CommitInstruction<N, O> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, commit) = CommitBHP512::<CurrentNetwork>::parse("commit.bhp512 r0 r1 into r2").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(commit.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(commit.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(commit.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(commit.destination, Register::Locator(2), "The destination register is incorrect");
    }
}
