// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
    Opcode,
    Operand,
};
use circuit::{Inject, Mode};
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
    types::U32,
};

/// Returns the length of an array or vector.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Length<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
}

impl<N: Network> Length<N> {
    /// Initializes a new `length` instruction.
    #[inline]
    pub fn new(operand: Operand<N>, destination: Register<N>) -> Self {
        // Return the instruction.
        Self { operands: vec![operand], destination }
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Length
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }
}

impl<N: Network> Length<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operand, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the input.
        let input = registers.load(stack, &self.operands[0])?;

        // Get the length of the array.
        let output = match input {
            Value::Plaintext(Plaintext::List(list, ..)) => match u32::try_from(list.len()) {
                Ok(len) => Literal::U32(U32::new(len)),
                Err(_) => bail!("Length exceeds u32::MAX"),
            },
            _ => bail!("`length` expects an array as input"),
        };

        // Store the output.
        registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(output)))
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operand, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the input.
        let input = registers.load_circuit(stack, &self.operands[0])?;

        // Get the length of the array.
        let output = match input {
            circuit::Value::Plaintext(circuit::Plaintext::<A>::List(list, ..)) => match u32::try_from(list.len()) {
                Ok(len) => circuit::Literal::U32(circuit::U32::new(Mode::Constant, U32::new(len))),
                Err(_) => bail!("Length exceeds u32::MAX"),
            },
            _ => bail!("`length` expects an array as input"),
        };
        // Convert the output to a stack value.
        let output = circuit::Value::Plaintext(circuit::Plaintext::Literal(output, Default::default()));
        // Store the output.
        registers.store_circuit(stack, &self.destination, output)
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 1 {
            bail!("Instruction '{}' expects 1 operand, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the input.
        let input = registers.load(stack, &self.operands[0])?;

        // Get the length of the array or vector.
        let output = match input {
            Value::Plaintext(Plaintext::List(list, ..)) => match u32::try_from(list.len()) {
                Ok(len) => Literal::U32(U32::new(len)),
                Err(_) => bail!("Length exceeds u32::MAX"),
            },
            _ => bail!("`length` expects an array or vector as input"),
        };

        // Store the output.
        registers.store(stack, &self.destination, Value::Plaintext(Plaintext::from(output)))
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 1 {
            bail!("Instruction '{}' expects 1 input, found {} inputs", Self::opcode(), input_types.len())
        }

        // Ensure that the input type is either an array or a vector.
        match input_types[0] {
            RegisterType::Plaintext(PlaintextType::Array(_)) | RegisterType::Vector(_) => {}
            _ => bail!("Instruction '{}' expects an array or vector as input", Self::opcode()),
        }

        Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U32))])
    }
}

impl<N: Network> Parser for Length<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, operand) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        // Return the operation.
        Ok((string, Self::new(operand, destination)))
    }
}

impl<N: Network> FromStr for Length<N> {
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

impl<N: Network> Debug for Length<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Length<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} {} into {}", Self::opcode(), self.operands[0], self.destination)
    }
}

impl<N: Network> FromBytes for Length<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the operand.
        let operand = Operand::read_le(&mut reader)?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self::new(operand, destination))
    }
}

impl<N: Network> ToBytes for Length<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 1.
        if self.operands.len() != 1 {
            return Err(error(format!("The number of operands must be 1, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands[0].write_le(&mut writer)?;
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
        let (string, length) = Length::<CurrentNetwork>::parse("length r0 into r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(length.operands.len(), 1);
        assert_eq!(length.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(length.destination, Register::Locator(1), "The destination register is incorrect");
    }
}
