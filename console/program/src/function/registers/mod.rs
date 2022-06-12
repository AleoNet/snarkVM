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

use crate::{function::instruction::Operand, Literal, Plaintext, PlaintextType, Program, Register, Value, ValueType};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
enum RegisterValue<N: Network> {
    /// An input value is a user-defined input that takes the visibility defined by the program.
    Input(Value<N, Plaintext<N>>),
    /// A destination value is the output of executing an instruction.
    Destination(Plaintext<N>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(in crate::function) enum RegisterType<N: Network> {
    /// An input register contains a plaintext value with visibility.
    Input(ValueType<N>),
    /// A destination register contains a plaintext value from an instruction.
    Destination(PlaintextType<N>),
}

/// The registers contains a mapping of the registers to their corresponding values in a function.
#[derive(Clone)]
pub(in crate::function) struct Registers<N: Network> {
    /// The mapping of all registers to their defined types.
    register_types: IndexMap<u64, RegisterType<N>>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, RegisterValue<N>>,
}

impl<N: Network> Registers<N> {
    /// Initializes a new instance of the registers, given:
    ///   1. The register types as defined by the function.
    ///   2. The input register values.
    ///
    /// # Errors
    /// This method will halt if any input type does not match the register type.
    #[inline]
    pub(in crate::function) fn new(
        program: &Program<N>,
        register_types: IndexMap<u64, RegisterType<N>>,
        inputs: &[Plaintext<N>],
    ) -> Result<Self> {
        // Initialize the registers.
        let mut registers = Self { register_types, registers: IndexMap::new() };

        // Determine the visibility of the inputs.
        for ((locator, register), input) in registers.register_types.iter().zip_eq(inputs.iter()) {
            // Ensure the register is an input register.
            match register {
                RegisterType::Input(value_type) => {
                    // Ensure the plaintext type of the input matches what is declared in the register.
                    input.matches(program, &value_type.to_plaintext_type())?;

                    // Construct a value out of the plaintext input.
                    let value = match value_type {
                        ValueType::Constant(..) => Value::Constant(input.clone()),
                        ValueType::Public(..) => Value::Public(input.clone()),
                        ValueType::Private(..) => Value::Private(input.clone()),
                    };

                    // Assign the input value to the register.
                    registers.registers.insert(*locator, RegisterValue::Input(value));
                }
                RegisterType::Destination(..) => bail!("Register {locator} is not an input register"),
            }

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.
        }

        Ok(registers)
    }

    /// Assigns the given literal to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the register was previously stored.
    #[inline]
    pub(in crate::function) fn store_literal(
        &mut self,
        program: &Program<N>,
        register: &Register<N>,
        literal: Literal<N>,
    ) -> Result<()> {
        self.store(program, register, Plaintext::from(literal))
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the register was previously stored.
    #[inline]
    pub(in crate::function) fn store(
        &mut self,
        program: &Program<N>,
        register: &Register<N>,
        plaintext: Plaintext<N>,
    ) -> Result<()> {
        // Ensure the register assignments are monotonically increasing.
        let expected_register = Register::Locator(self.registers.len() as u64);
        ensure!(expected_register == *register, "Expected '{expected_register}', found '{register}'");

        // Retrieve the register type.
        let register_type = match self.register_types.get(&register.locator()) {
            Some(register_type) => register_type,
            None => bail!("Register {register} is not a member of the function"),
        };

        // Ensure the register type is not an input register.
        match register_type {
            RegisterType::Input(..) => bail!("Cannot store to input '{register}', expected a destination register"),
            // Ensure the plaintext type is the expected type.
            RegisterType::Destination(plaintext_type) => plaintext.matches(program, &plaintext_type)?,
        }

        // Store the plaintext in the register.
        let previous = match register {
            // Store the plaintext for a register.
            Register::Locator(locator) => self.registers.insert(*locator, RegisterValue::Destination(plaintext)),
            // Store the plaintext for a register member.
            Register::Member(..) => bail!("Cannot store directly to \'{register}\'"),
        };

        // Ensure the register has not been previously stored.
        match previous {
            Some(..) => bail!("Register \'{register}\' was previously assigned"),
            None => Ok(()),
        }
    }

    /// Loads the literal of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub(in crate::function) fn load_literal(&self, program: &Program<N>, operand: &Operand<N>) -> Result<Literal<N>> {
        match self.load(program, operand)? {
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
    pub(in crate::function) fn load(&self, program: &Program<N>, operand: &Operand<N>) -> Result<Plaintext<N>> {
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
