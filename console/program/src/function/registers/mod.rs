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

use crate::{function::instruction::Operand, Literal, Plaintext, PlaintextType, Register, Value, ValueType};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
enum RegisterValue<N: Network> {
    Input(Value<N, Plaintext<N>>),
    Destination(Plaintext<N>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(in crate::function) enum RegisterType<N: Network> {
    Input(ValueType<N>),
    Destination(PlaintextType<N>),
}

impl<N: Network> RegisterType<N> {
    /// Returns `true` if `self` is an input register.
    pub(in crate::function) const fn is_input(&self) -> bool {
        matches!(self, Self::Input(..))
    }

    /// Returns `true` if `self` is a destination register.
    pub(in crate::function) const fn is_destination(&self) -> bool {
        matches!(self, Self::Destination(..))
    }
}

/// The registers contains a mapping of the registers to their corresponding values in a function.
#[derive(Clone)]
pub(in crate::function) struct Registers<N: Network> {
    /// The mapping of registers to their types.
    register_types: IndexMap<u64, RegisterType<N>>,
    /// The mapping of registers to their values.
    registers: IndexMap<u64, RegisterValue<N>>,
    /// The number of registers assigned in the function.
    num_assigned: u64,
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
        register_types: IndexMap<u64, RegisterType<N>>,
        inputs: &[Plaintext<N>],
    ) -> Result<Self> {
        // Initialize the registers.
        let mut registers = Self { register_types, registers: IndexMap::new(), num_assigned: 0 };

        // Determine the visibility of the inputs.
        for ((locator, register), input) in registers.register_types.iter().zip_eq(inputs.iter()) {
            // Ensure the register is an input register.

            match register {
                RegisterType::Input(value_type) => {
                    // Ensure the plaintext type of the input matches what is declared in the register.
                    // ensure!(input.to_type() == value_type.to_plaintext_type(), "Input register type does not match");

                    // Construct a value out of the plaintext input.
                    let value = match value_type {
                        ValueType::Constant(plaintext_type) => Value::Constant(input.clone()),
                        ValueType::Public(plaintext_type) => Value::Public(input.clone()),
                        ValueType::Private(plaintext_type) => Value::Private(input.clone()),
                    };

                    // Assign the input value to the register.
                    registers.registers.insert(*locator, RegisterValue::Input(value));
                }
                RegisterType::Destination(..) => bail!("Register {locator} is not an input register"),
            }

            // // If the input annotation is a definition, ensure the input value matches the definition.
            // if let Annotation::Definition(definition_name) = input.annotation() {
            //     // Retrieve the definition from the program.
            //     match P::get_definition(definition_name) {
            //         // Ensure the value matches its expected definition.
            //         Some(definition) => {
            //             if !definition.matches(value) {
            //                 P::halt(format!("Input \'{register}\' does not match \'{definition_name}\'"))
            //             }
            //         }
            //         None => P::halt("Input \'{register}\' references a non-existent definition"),
            //     }
            // }

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
    pub(in crate::function) fn store_literal(&mut self, register: &Register<N>, literal: Literal<N>) -> Result<()> {
        // Ensure the register assignments are monotonically increasing.
        ensure!(
            self.num_assigned == register.locator(),
            "Expected \'{}\', found \'{register}\'",
            Register::<N>::Locator(self.num_assigned)
        );

        // Retrieve the register type.
        let register_type = self
            .register_types
            .get(&register.locator())
            .ok_or_else(|| anyhow!("Register {} is not a member of the function", register.locator()))?;
        // Ensure the register type is not an input register.
        ensure!(register_type.is_destination(), "Cannot store to input {register}, expected a destination register");

        // Store the literal in the register.
        let previous = match register {
            // Store the literal for a register.
            Register::Locator(locator) => {
                self.registers.insert(*locator, RegisterValue::Destination(Plaintext::from(literal)))
            }
            // Store the literal for a register member.
            Register::Member(..) => bail!("Cannot store directly to \'{register}\'"),
        };

        // Ensure the register has not been previously stored.
        match previous {
            // Halt if the register was previously stored.
            Some(..) => bail!("Register \'{register}\' was previously assigned"),
            // Increment the number of assigned registers.
            None => self.num_assigned += 1,
        }
        Ok(())
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the register was previously stored.
    #[inline]
    pub(in crate::function) fn store(&mut self, register: &Register<N>, plaintext: Plaintext<N>) -> Result<()> {
        // Ensure the register assignments are monotonically increasing.
        ensure!(
            self.num_assigned == register.locator(),
            "Expected \'{}\', found \'{register}\'",
            Register::<N>::Locator(self.num_assigned)
        );

        // Retrieve the register type.
        let register_type = self
            .register_types
            .get(&register.locator())
            .ok_or_else(|| anyhow!("Register {} is not a member of the function", register.locator()))?;
        // Ensure the register type is not an input register.
        ensure!(register_type.is_destination(), "Cannot store to input {register}, expected a destination register");

        // Store the plaintext in the register.
        let previous = match register {
            // Store the plaintext for a register.
            Register::Locator(locator) => self.registers.insert(*locator, RegisterValue::Destination(plaintext)),
            // Store the plaintext for a register member.
            Register::Member(..) => bail!("Cannot store directly to \'{register}\'"),
        };

        // Ensure the register has not been previously stored.
        match previous {
            // Halt if the register was previously stored.
            Some(..) => bail!("Register \'{register}\' was previously assigned"),
            // Increment the number of assigned registers.
            None => self.num_assigned += 1,
        }
        Ok(())
    }

    /// Loads the literal of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub(in crate::function) fn load_literal(&self, operand: &Operand<N>) -> Result<Literal<N>> {
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
    pub(in crate::function) fn load(&self, operand: &Operand<N>) -> Result<Plaintext<N>> {
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
            Register::Member(_, ref identifiers) => {
                unimplemented!("Register member loading is not yet implemented")
                // match value {
                // // Halts if the value is not an interface.
                // Plaintext::Literal(..) => bail!("Cannot load a register member from a literal"),
                // // Retrieve the value of the member (from the value).
                // Plaintext::Interface(mut interface, mut member_values) => {
                //     // Iterate through all of the identifiers to retrieve the value.
                //     for (i, identifier) in identifiers.iter().enumerate() {
                //         // Retrieve the member index and value type of the identifier (from the interface).
                //         let (member_index, member_value_type) = match P::get_interface(&interface) {
                //             Some(interface) => interface
                //                 .members()
                //                 .iter()
                //                 .enumerate()
                //                 .filter_map(|(member_index, member)| match member.name() == identifier {
                //                     true => Some((member_index, member.value_type().clone())),
                //                     false => None,
                //                 })
                //                 .next()
                //                 .unwrap_or_else(|| {
                //                     bail!("Failed to locate '{register}': missing '{identifier}' in '{interface}'")
                //                 }),
                //             // Halts if the interface does not exist.
                //             None => bail!("Failed to locate '{register}': missing '{interface}'"),
                //         };
                //
                //         // For a standard round (that is not the last round), update the `interface` and `member_values` for the next round.
                //         if i < identifiers.len() - 1 {
                //             // Set the `interface`.
                //             match member_value_type {
                //                 // If the value type is a literal, then halt as this should not be possible since it is not the last round.
                //                 PlaintextType::Literal(..) => bail!("Cannot load a literal from a register member"),
                //                 // If the value type is a interface, update the `interface` to the next name.
                //                 PlaintextType::Interface(name) => interface = name.clone(),
                //             }
                //
                //             // Set the `member_values`.
                //             match member_values.get(member_index) {
                //                 Some(member_value) => match member_value {
                //                     // If the value is a literal, then halt as this should not be possible since it is not the last round.
                //                     Plaintext::Literal(..) => bail!("Cannot load a literal from a register member"),
                //                     // If the value is a interface, update the `member_values` to the next list of member values.
                //                     Plaintext::Interface(_, members) => member_values = (*members).clone(),
                //                 },
                //                 // Halts if the member does not exist.
                //                 None => bail!("Failed to locate '{register}': invalid member index"),
                //             }
                //         }
                //         // If this is the last round, then retrieve and return the value.
                //         else {
                //             // Return the value of the member.
                //             match member_values.get(member_index) {
                //                 Some(value) => return (*value).clone(),
                //                 // Halts if the member does not exist.
                //                 None => bail!("Failed to locate \'{register}\'"),
                //             }
                //         }
                //     }
                //
                //     bail!("Failed to locate \'{register}\'")
                // }
            }
        }
    }
}
