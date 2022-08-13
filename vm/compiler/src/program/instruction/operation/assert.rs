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

use crate::{Opcode, Operand, Registers, Stack};
use console::{
    network::prelude::*,
    program::{Register, RegisterType},
};

/// Asserts two operands are equal to each other.
pub type AssertEq<N> = AssertInstruction<N, { Variant::AssertEq as u8 }>;
/// Asserts two operands are **not** equal to each other.
pub type AssertNeq<N> = AssertInstruction<N, { Variant::AssertNeq as u8 }>;

enum Variant {
    AssertEq,
    AssertNeq,
}

/// Asserts an operation on two operands.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AssertInstruction<N: Network, const VARIANT: u8> {
    /// The operand as `input`.
    operands: Vec<Operand<N>>,
}

impl<N: Network, const VARIANT: u8> AssertInstruction<N, VARIANT> {
    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        match VARIANT {
            0 => Opcode::Assert("assert.eq"),
            1 => Opcode::Assert("assert.neq"),
            _ => panic!("Invalid 'assert' instruction opcode"),
        }
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that the operands is exactly two inputs.
        debug_assert!(self.operands.len() == 2, "Assert operations must have two operands");
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![]
    }
}

impl<N: Network, const VARIANT: u8> AssertInstruction<N, VARIANT> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Load the operands values.
        let inputs: Vec<_> = self.operands.iter().map(|operand| registers.load(stack, operand)).try_collect()?;
        // Retrieve the inputs.
        let (input_a, input_b) = (inputs[0].clone(), inputs[1].clone());

        // Assert the inputs.
        match VARIANT {
            0 => {
                if input_a != input_b {
                    bail!("'{}' failed: '{input_a}' is not equal to '{input_b}' (should be equal)", Self::opcode())
                }
            }
            1 => {
                if input_a == input_b {
                    bail!("'{}' failed: '{input_a}' is equal to '{input_b}' (should not be equal)", Self::opcode())
                }
            }
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
        Ok(())
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &Stack<N>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Load the operands values.
        let inputs: Vec<_> =
            self.operands.iter().map(|operand| registers.load_circuit(stack, operand)).try_collect()?;
        // Retrieve the inputs.
        let (input_a, input_b) = (inputs[0].clone(), inputs[1].clone());

        // Assert the inputs.
        match VARIANT {
            0 => A::assert(input_a.is_equal(&input_b)),
            1 => A::assert(input_a.is_not_equal(&input_b)),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
        Ok(())
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(&self, _stack: &Stack<N>, input_types: &[RegisterType<N>]) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", Self::opcode(), input_types.len())
        }
        // Ensure the operands are of the same type.
        if input_types[0] != input_types[1] {
            bail!(
                "Instruction '{}' expects inputs of the same type, found inputs of type {} and {}",
                Self::opcode(),
                input_types[0],
                input_types[1]
            )
        }
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        match VARIANT {
            0 | 1 => Ok(vec![]),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
    }
}

impl<N: Network, const VARIANT: u8> Parser for AssertInstruction<N, VARIANT> {
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

        Ok((string, Self { operands: vec![first, second] }))
    }
}

impl<N: Network, const VARIANT: u8> FromStr for AssertInstruction<N, VARIANT> {
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

impl<N: Network, const VARIANT: u8> Debug for AssertInstruction<N, VARIANT> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, const VARIANT: u8> Display for AssertInstruction<N, VARIANT> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            eprintln!("The number of operands must be 2, found {}", self.operands.len());
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{} ", operand))
    }
}

impl<N: Network, const VARIANT: u8> FromBytes for AssertInstruction<N, VARIANT> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }

        // Return the operation.
        Ok(Self { operands })
    }
}

impl<N: Network, const VARIANT: u8> ToBytes for AssertInstruction<N, VARIANT> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, assert) = AssertEq::<CurrentNetwork>::parse("assert.eq r0 r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(assert.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(assert.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(assert.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");

        let (string, assert) = AssertNeq::<CurrentNetwork>::parse("assert.neq r0 r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(assert.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(assert.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(assert.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
    }
}
