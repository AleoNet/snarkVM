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
    Entry,
    Identifier,
    Literal,
    Plaintext,
    PlaintextType,
    Program,
    Record,
    Register,
    Value,
    ValueType,
};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub enum RegisterValue<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value.
    Record(Record<N, Plaintext<N>>),
}

#[derive(Clone)]
pub struct Stack<N: Network> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned input registers to their values.
    input_registers: IndexMap<u64, Value<N, Plaintext<N>>>,
    /// The mapping of assigned destination registers to their values.
    destination_registers: IndexMap<u64, RegisterValue<N>>,
}

impl<N: Network> Stack<N> {
    /// Initializes a new stack with:
    ///   1. The program (record types, interfaces, functions).
    ///   2. The register types of the function.
    ///   3. The input register values.
    ///
    /// # Errors
    /// This method will halt if any input type does not match the register type.
    #[inline]
    pub fn new(program: Program<N>, register_types: RegisterTypes<N>, inputs: &[RegisterValue<N>]) -> Result<Self> {
        // Initialize the stack.
        let mut stack =
            Self { program, register_types, input_registers: IndexMap::new(), destination_registers: IndexMap::new() };

        // Determine the visibility of the inputs.
        for ((input_register, value_type), input) in stack.register_types.to_inputs().zip_eq(inputs.iter()) {
            // Ensure the input value matches the declared type in the register.
            stack.matches_input(input, &value_type)?;

            // TODO (howardwu): If input is a record, add all the safety hooks we need to use the record data.

            // Assign the input value to the register.
            stack.input_registers.insert(input_register.locator(), match (input.clone(), value_type) {
                (RegisterValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
                (RegisterValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
                (RegisterValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
                (RegisterValue::Record(record), ValueType::Record(..)) => Value::Record(record),
                _ => bail!("Input value does not match the input register type."),
            });
        }

        Ok(stack)
    }
}

impl<N: Network> Stack<N> {
    /// Returns `true` if the given register corresponds to an input register.
    fn is_input(&self, register: &Register<N>) -> bool {
        self.input_registers.contains_key(&register.locator())
    }

    /// Assigns the given literal to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub(crate) fn store_literal(&mut self, register: &Register<N>, literal: Literal<N>) -> Result<()> {
        self.store(register, RegisterValue::Plaintext(Plaintext::from(literal)))
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub(crate) fn store(&mut self, register: &Register<N>, register_value: RegisterValue<N>) -> Result<()> {
        match register {
            Register::Locator(locator) => {
                // Ensure the register assignments are monotonically increasing.
                let expected_locator = (self.input_registers.len() as u64) + self.destination_registers.len() as u64;
                ensure!(expected_locator == *locator, "Out-of-order write operation at '{register}'");
                // Ensure the register type is not an input register.
                ensure!(!self.register_types.is_input(register), "Cannot write to input register '{register}'");

                // Retrieve the register type.
                match self.register_types.get_type(&self.program, register) {
                    // Ensure the register value matches the register type.
                    Ok(register_type) => self.matches_register(&register_value, &register_type)?,
                    // Ensure the register is defined.
                    Err(error) => bail!("Register '{register}' is not a member of the function: {error}"),
                };

                // Store the register value.
                match self.destination_registers.insert(*locator, register_value) {
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
    pub(crate) fn load_literal(&self, operand: &Operand<N>) -> Result<Literal<N>> {
        match self.load(operand)? {
            RegisterValue::Plaintext(Plaintext::Literal(literal, ..)) => Ok(literal),
            RegisterValue::Plaintext(Plaintext::Interface(..)) => bail!("Operand must be a literal"),
            RegisterValue::Record(..) => bail!("Operand must be a literal"),
        }
    }

    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub(crate) fn load(&self, operand: &Operand<N>) -> Result<RegisterValue<N>> {
        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => return Ok(RegisterValue::Plaintext(Plaintext::from(literal))),
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
        };

        // Retrieve the register value.
        let register_value = if self.is_input(register) {
            // Retrieve the input value type as a register type.
            match self.input_registers.get(&register.locator()).ok_or_else(|| anyhow!("'{register}' does not exist"))? {
                Value::Constant(plaintext) | Value::Public(plaintext) | Value::Private(plaintext) => {
                    RegisterValue::Plaintext(plaintext.clone())
                }
                Value::Record(record) => RegisterValue::Record(record.clone()),
            }
        } else {
            // Retrieve the destination register type.
            self.destination_registers
                .get(&register.locator())
                .ok_or_else(|| anyhow!("'{register}' does not exist"))?
                .clone()
        };

        // Return the value for the given register or register member.
        match register {
            // If the register is a locator, then return the plaintext value.
            Register::Locator(..) => Ok(register_value),
            // If the register is a register member, then load the specific plaintext value.
            Register::Member(_, ref path) => {
                match register_value {
                    // Retrieve the plaintext member from the path.
                    RegisterValue::Plaintext(plaintext) => Ok(RegisterValue::Plaintext(plaintext.find(path)?)),
                    // Retrieve the record entry from the path.
                    RegisterValue::Record(record) => match record.find(path)? {
                        Entry::Constant(plaintext) | Entry::Public(plaintext) | Entry::Private(plaintext) => {
                            Ok(RegisterValue::Plaintext(plaintext))
                        }
                    },
                }
            }
        }
    }
}
