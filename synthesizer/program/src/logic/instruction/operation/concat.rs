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
use circuit::Eject;
use console::{
    network::prelude::*,
    program::{ArrayType, Plaintext, PlaintextType, Register, RegisterType, Value},
};

/// Concatenates `first` and `second`, storing the outcome in `destination`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Concat<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    /// The target type.
    target_type: ArrayType<N>,
}

impl<N: Network> Concat<N> {
    /// Initializes a new `concat` instruction.
    #[inline]
    pub fn new(operands: Vec<Operand<N>>, destination: Register<N>, target_type: ArrayType<N>) -> Result<Self> {
        // Sanity check the number of operands.
        ensure!(operands.len() == 2, "Instruction '{}' must have two operands", Self::opcode());
        // Return the instruction.
        Ok(Self { operands, destination, target_type })
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::Concat
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that there are exactly three operands.
        debug_assert!(self.operands.len() == 2, "Instruction '{}' must have two operands", Self::opcode());
        // Return the operands.
        &self.operands
    }

    /// Returns the destination register.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone()]
    }

    /// Returns the target type.
    #[inline]
    pub fn target_type(&self) -> &ArrayType<N> {
        &self.target_type
    }
}

impl<N: Network> Concat<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs, ensuring that they are arrays.
        let mut first = match registers.load(stack, &self.operands[0])? {
            Value::Plaintext(Plaintext::Array(first, _)) => first,
            _ => bail!("Expected the first operand to be an array."),
        };
        let mut second = match registers.load(stack, &self.operands[1])? {
            Value::Plaintext(Plaintext::Array(second, _)) => second,
            _ => bail!("Expected the second operand to be an array."),
        };

        // Ensure that the sum of the lengths of the arrays match the target type.
        ensure!(
            first.len() + second.len() == **self.target_type.length() as usize,
            "Expected the sum of the lengths of the arrays to match the target type."
        );

        // Ensure that the elements of the arrays match the target element type.
        for element in first.iter() {
            stack.matches_plaintext(element, self.target_type.next_element_type())?;
        }
        for element in second.iter() {
            stack.matches_plaintext(element, self.target_type.next_element_type())?;
        }

        // Concatenate the arrays.
        first.append(&mut second);
        let output = Value::Plaintext(Plaintext::Array(first, Default::default()));

        // Store the output.
        registers.store(stack, &self.destination, output)
    }

    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs, ensuring that they are arrays.
        let mut first = match registers.load_circuit(stack, &self.operands[0])? {
            circuit::Value::Plaintext(circuit::Plaintext::Array(first, _)) => first,
            _ => bail!("Expected the first operand to be an array."),
        };
        let mut second = match registers.load_circuit(stack, &self.operands[1])? {
            circuit::Value::Plaintext(circuit::Plaintext::Array(second, _)) => second,
            _ => bail!("Expected the second operand to be an array."),
        };

        // Ensure that the sum of the lengths of the arrays match the target type.
        ensure!(
            first.len() + second.len() == **self.target_type.length() as usize,
            "Expected the sum of the lengths of the arrays to match the target type."
        );

        // Ensure that the elements of the arrays match the target element type.
        for element in first.iter() {
            stack.matches_plaintext(&element.eject_value(), self.target_type.next_element_type())?;
        }
        for element in second.iter() {
            stack.matches_plaintext(&element.eject_value(), self.target_type.next_element_type())?;
        }

        // Concatenate the arrays.
        first.append(&mut second);
        let output = circuit::Value::Plaintext(circuit::Plaintext::Array(first, Default::default()));

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
        self.evaluate(stack, registers)
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

        // Ensure the first operand is an array.
        let first_type = match &input_types[0] {
            RegisterType::Plaintext(PlaintextType::Array(first_type)) => first_type,
            _ => bail!(
                "Instruction '{}' expects the first input to be an 'array'. Found input of type '{}'",
                Self::opcode(),
                input_types[0]
            ),
        };

        // Ensure the second operand is an array.
        let second_type = match &input_types[1] {
            RegisterType::Plaintext(PlaintextType::Array(second_type)) => second_type,
            _ => bail!(
                "Instruction '{}' expects the second input to be an 'array'. Found input of type '{}'",
                Self::opcode(),
                input_types[1]
            ),
        };

        // Check that the sum of the lengths of the arrays match the target type.
        if **first_type.length() + **second_type.length() != **self.target_type.length() {
            bail!("Expected the sum of the lengths of the arrays to match the target type.")
        }

        // Check that the element types of the arrays match the target element type.
        if first_type.next_element_type() != self.target_type.next_element_type() {
            bail!("Expected the element types of the first array to match the target element type.")
        }
        if second_type.next_element_type() != self.target_type.next_element_type() {
            bail!("Expected the element types of the second array to match the target element type.")
        }

        Ok(vec![RegisterType::Plaintext(PlaintextType::Array(self.target_type.clone()))])
    }
}

impl<N: Network> Parser for Concat<N> {
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
        // Parse the "as" from the string.
        let (string, _) = tag("as")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the target type from the string.
        let (string, target_type) = ArrayType::parse(string)?;

        Ok((string, Self { operands: vec![first, second], destination, target_type }))
    }
}

impl<N: Network> FromStr for Concat<N> {
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

impl<N: Network> Debug for Concat<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Concat<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} as {}", self.destination, self.target_type)
    }
}

impl<N: Network> FromBytes for Concat<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(3);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Read the target type.
        let target_type = ArrayType::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination, target_type })
    }
}

impl<N: Network> ToBytes for Concat<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer)?;
        // Write the target type.
        self.target_type.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() {
        let (string, concat) = Concat::<CurrentNetwork>::parse("concat r0 r1 into r2 as [boolean; 2u32]").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(concat.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(concat.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(concat.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(concat.destination, Register::Locator(2), "The destination register is incorrect");
        assert_eq!(
            concat.target_type,
            ArrayType::new(PlaintextType::Literal(LiteralType::Boolean), vec![console::program::U32::new(2)]),
            "The target type is incorrect"
        );
    }
}
