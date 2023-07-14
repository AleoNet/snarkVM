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
    program::{Plaintext, Register, RegisterType, Value},
};

/// Pushes an element to the end of a vector.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Push<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
}

impl<N: Network> Push<N> {
    /// Initializes a new `push` instruction.
    #[inline]
    pub fn new(register: Register<N>, element: Operand<N>) -> Self {
        // Return the instruction.
        Self { operands: vec![Operand::Register(register), element] }
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Push
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![]
    }
}

impl<N: Network> Push<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        _: &(impl StackMatches<N> + StackProgram<N>),
        _: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        bail!("`push` is currently only supported in `finalize`")
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        _: &(impl StackMatches<N> + StackProgram<N>),
        _: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        bail!("`push` is currently only supported in `finalize`")
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
            _ => bail!("`push` expects a vector as the first input"),
        };
        let element = match registers.load(stack, &self.operands[1])? {
            Value::Plaintext(plaintext) => plaintext,
            _ => bail!("`push` expects plaintext as the second input"),
        };

        // Push the element onto vector.
        vector.push(element);

        // Construct the output.
        let output = Plaintext::List(vector, Default::default());

        // Store the output.
        registers.store(stack, register, Value::Plaintext(output))
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
            _ => bail!("`push` expects a vector as the first input"),
        };

        // Ensure the second input type matches the vector element type.
        match input_types[1] {
            RegisterType::Plaintext(plaintext_type) => {
                if plaintext_type != *vector_type.element_type() {
                    bail!("`push` expects the second input to be a '{}'", vector_type.element_type())
                }
            }
            _ => bail!("`push` expects plaintext as the second input"),
        }

        Ok(vec![])
    }
}

impl<N: Network> Parser for Push<N> {
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

        // Return the operation.
        Ok((string, Self::new(register, operand)))
    }
}

impl<N: Network> FromStr for Push<N> {
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

impl<N: Network> Debug for Push<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Push<N> {
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
        write!(f, "{} {} {}", Self::opcode(), register, self.operands[1])
    }
}

impl<N: Network> FromBytes for Push<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the register.
        let register = Register::read_le(&mut reader)?;
        // Read the element.
        let element = Operand::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self::new(register, element))
    }
}

impl<N: Network> ToBytes for Push<N> {
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
        self.operands[1].write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, push) = Push::<CurrentNetwork>::parse("push r0 r1").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(push.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(push.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert!(push.destinations().is_empty());
    }
}
