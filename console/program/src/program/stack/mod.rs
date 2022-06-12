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

mod matches;

use crate::{
    function::Operand,
    program::{RegisterType, RegisterTypes},
    Literal,
    Plaintext,
    PlaintextType,
    Program,
    Register,
    Value,
    ValueType,
};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
enum RegisterValue<N: Network> {
    /// An input value is a user-defined input that takes the visibility defined by the program.
    Input(Value<N, Plaintext<N>>),
    /// A destination value is the output of executing an instruction.
    Destination(Plaintext<N>),
}

#[derive(Clone)]
pub struct Stack<N: Network> {
    /// The program this stack belongs to.
    program: Program<N>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, RegisterValue<N>>,
}

impl<N: Network> Stack<N> {
    /// Initializes a new stack with:
    ///   1. The program.
    ///   2. The register types for the function being executed.
    ///   3. The input register values.
    ///
    /// # Errors
    /// This method will halt if any input type does not match the register type.
    #[inline]
    pub fn new(program: Program<N>, register_types: RegisterTypes<N>, inputs: &[Plaintext<N>]) -> Result<Self> {
        // Initialize the registers.
        let mut stack = Self { program, register_types, registers: IndexMap::new() };

        // Determine the visibility of the inputs.
        for ((register, register_type), input) in stack.register_types.to_inputs().zip_eq(inputs.iter()) {
            // Ensure the register is an input register.
            match register_type {
                RegisterType::Input(value_type) => {
                    // Ensure the plaintext type of the input matches what is declared in the register.
                    stack.matches(input, &value_type.to_plaintext_type())?;

                    // Construct the register value with the plaintext input.
                    let register_value = match value_type {
                        ValueType::Constant(..) => RegisterValue::Input(Value::Constant(input.clone())),
                        ValueType::Public(..) => RegisterValue::Input(Value::Public(input.clone())),
                        ValueType::Private(..) => RegisterValue::Input(Value::Private(input.clone())),
                    };

                    // Assign the input value to the register.
                    stack.registers.insert(register.locator(), register_value);
                }
                RegisterType::Destination(..) => bail!("'{register}' is not an input register"),
            }

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
        }

        Ok(stack)
    }

    /// Assigns the given literal to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store_literal(&mut self, register: &Register<N>, literal: Literal<N>) -> Result<()> {
        self.store(register, Plaintext::from(literal))
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store(&mut self, register: &Register<N>, plaintext: Plaintext<N>) -> Result<()> {
        match register {
            Register::Locator(locator) => {
                // Ensure the register assignments are monotonically increasing.
                ensure!(self.registers.len() as u64 == *locator, "Out-of-order write operation at '{register}'");
                // Ensure the register type is not an input register.
                ensure!(!self.register_types.is_input(register), "Cannot write to input register '{register}'");

                // Retrieve the register type.
                match self.register_types.get_type(&self.program, register) {
                    // Ensure the plaintext type matches the register type.
                    Ok(plaintext_type) => self.matches(&plaintext, &plaintext_type)?,
                    // Ensure the register is defined.
                    Err(error) => bail!("Register '{register}' is not a member of the function: {error}"),
                };

                // Store the plaintext in the register.
                match self.registers.insert(*locator, RegisterValue::Destination(plaintext)) {
                    // Ensure the register has not been previously stored.
                    Some(..) => bail!("Attempted to write to register '{register}' again"),
                    // Return on success.
                    None => Ok(()),
                }
            }
            // Ensure the register is not a register member.
            Register::Member(..) => bail!("Cannot store to a register member: '{register}'"),
        }
    }

    /// Loads the literal of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load_literal(&self, operand: &Operand<N>) -> Result<Literal<N>> {
        match self.load(operand)? {
            Plaintext::Literal(literal, ..) => Ok(literal),
            Plaintext::Interface(..) => bail!("Operand must be a literal"),
        }
    }

    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load(&self, operand: &Operand<N>) -> Result<Plaintext<N>> {
        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => return Ok(Plaintext::from(literal)),
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
        };

        // Retrieve the plaintext from the register.
        let plaintext = match self.registers.get(&register.locator()) {
            // Return the value if it exists.
            Some(value) => match value {
                RegisterValue::Input(value) => value.to_plaintext(),
                RegisterValue::Destination(plaintext) => plaintext,
            },
            // Halts if the register value does not exist.
            None => bail!("Failed to locate register '{register}'"),
        };

        // Return the value for the given register or register member.
        match register {
            // If the register is a locator, then return the plaintext value.
            Register::Locator(..) => Ok(plaintext.clone()),
            // If the register is a register member, then load the specific plaintext value.
            Register::Member(_, ref path) => {
                match plaintext {
                    // Halts if the value is not an interface.
                    Plaintext::Literal(..) => bail!("Register '{register}' is not an interface"),
                    // Retrieve the value of the member (from the value).
                    Plaintext::Interface(members, ..) => {
                        // Initialize the members starting from the top-level.
                        let mut submembers = members;

                        // Initialize the output.
                        let mut output = None;

                        // Iterate through the path to retrieve the value.
                        for (i, identifier) in path.iter().enumerate() {
                            // If this is not the last item in the path, ensure the value is an interface.
                            if i != path.len() - 1 {
                                match submembers.get(identifier) {
                                    // Halts if the member does not exist.
                                    None => bail!("Failed to locate member '{identifier}' in register '{register}'"),
                                    // Halts if the member is not an interface.
                                    Some(Plaintext::Literal(..)) => {
                                        bail!("'{identifier}' in register '{register}' is not an interface")
                                    }
                                    // Retrieve the member and update `submembers` for the next iteration.
                                    Some(Plaintext::Interface(members, ..)) => submembers = members,
                                }
                            }
                            // Otherwise, return the final member.
                            else {
                                match submembers.get(identifier) {
                                    // Return the plaintext member.
                                    Some(plaintext) => output = Some(plaintext.clone()),
                                    // Halts if the member does not exist.
                                    None => bail!("Failed to locate member '{identifier}' in register '{register}'"),
                                }
                            }
                        }

                        // Return the output.
                        match output {
                            Some(output) => Ok(output),
                            None => bail!("Failed to locate register '{register}'"),
                        }
                    }
                }
            }
        }
    }
}
