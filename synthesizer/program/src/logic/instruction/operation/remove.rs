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
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

/// Removes an element at the given index..
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Remove<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register
    destination: Register<N>,
}

impl<N: Network> Remove<N> {
    /// Initializes a new `remove` instruction.
    #[inline]
    pub fn new(register: Register<N>, element: Operand<N>, destination: Register<N>) -> Self {
        // Return the instruction.
        Self { operands: vec![Operand::Register(register), element], destination }
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Remove
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

impl<N: Network> Remove<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        _: &(impl StackMatches<N> + StackProgram<N>),
        _: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        bail!("`remove` is currently only supported in `finalize`")
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        _: &(impl StackMatches<N> + StackProgram<N>),
        _: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        bail!("`remove` is currently only supported in `finalize`")
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Get the register.
        let register = match &self.operands[0] {
            Operand::Register(register) => register,
            _ => bail!("`push` expects a register as the first operand"),
        };

        // Retrieve the input.
        let mut vector = match registers.load(stack, &self.operands[0])? {
            Value::Plaintext(Plaintext::List(list, ..)) => list,
            _ => bail!("`remove` expects a vector as the first input"),
        };
        let index = match registers.load(stack, &self.operands[1])? {
            Value::Plaintext(Plaintext::Literal(Literal::U32(index), ..)) => *index as usize,
            _ => bail!("`remove` expects a u32 as the second input"),
        };

        // Remove the element from vector.
        let output = match index < vector.len() {
            true => vector.remove(index),
            false => bail!("`remove` index '{index}' out of bounds"),
        };

        // Store the output in the destination register.
        registers.store(stack, &self.destination, Value::Plaintext(output))?;
        // Store the modified vector in its original location.
        registers.store(stack, register, Value::Plaintext(Plaintext::List(vector, Default::default())))
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", Self::opcode(), input_types.len())
        }

        // Ensure the first input type is a vector.
        let vector_type = match input_types[0] {
            RegisterType::Vector(vector_type) => vector_type,
            _ => bail!("`remove` expects a vector as the first input"),
        };

        // Ensure the second input type matches the vector element type.
        match input_types[1] {
            RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U32)) => {}
            _ => bail!("`remove` expects a u32 as the second input"),
        }

        Ok(vec![RegisterType::Plaintext(*vector_type.element_type())])
    }
}

impl<N: Network> Parser for Remove<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the register from the string.
        let (string, register) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the operand from the string.
        let (string, operand) = Operand::parse(string)?;

        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the `into` keyword from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;

        // Return the operation.
        Ok((string, Self::new(register, operand, destination)))
    }
}

impl<N: Network> FromStr for Remove<N> {
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

impl<N: Network> Debug for Remove<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Remove<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(fmt::Error);
        }
        // Ensure the first operand is a register.
        let register = match &self.operands[0] {
            Operand::Register(register) => register,
            _ => return Err(fmt::Error),
        };
        // Print the operation.
        write!(f, "{} {} {} into {}", Self::opcode(), register, self.operands[1], self.destination)
    }
}

impl<N: Network> FromBytes for Remove<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the register.
        let register = Register::read_le(&mut reader)?;
        // Read the element.
        let element = Operand::read_le(&mut reader)?;
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self::new(register, element, destination))
    }
}

impl<N: Network> ToBytes for Remove<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Ensure that the first operand is a register.
        let register = match &self.operands[0] {
            Operand::Register(register) => register,
            operand => return Err(error(format!("The first operand must be a register, found {operand}"))),
        };
        // Write the register.
        register.write_le(&mut writer)?;
        // Write the second operand.
        self.operands[1].write_le(&mut writer)?;
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
        let (string, remove) = Remove::<CurrentNetwork>::parse("remove r0 r1 into r2").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(remove.operands.len(), 2);
        assert_eq!(remove.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(remove.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(remove.destination, Register::Locator(2), "The destination register is incorrect");
    }
}
