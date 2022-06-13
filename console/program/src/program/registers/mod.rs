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

use crate::{Identifier, PlaintextType, Program, Register, ValueType};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum RegisterType<N: Network> {
    /// A plaintext type.
    Plaintext(PlaintextType<N>),
    /// A record name.
    Record(Identifier<N>),
}

impl<N: Network> Display for RegisterType<N> {
    /// Prints the register type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the plaintext type, i.e. signature
            Self::Plaintext(plaintext_type) => write!(f, "{plaintext_type}"),
            // Prints the record name, i.e. token.record
            Self::Record(record_name) => write!(f, "{record_name}.record"),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct RegisterTypes<N: Network> {
    /// The mapping of all input registers to their defined types.
    input_registers: IndexMap<u64, ValueType<N>>,
    /// The mapping of all destination registers to their defined types.
    destination_registers: IndexMap<u64, RegisterType<N>>,
    /// The mapping of all output registers to their defined types.
    output_registers: IndexMap<Register<N>, ValueType<N>>,
}

impl<N: Network> RegisterTypes<N> {
    /// Initializes a new instance of `RegisterTypes`.
    pub fn new() -> Self {
        Self {
            input_registers: IndexMap::new(),
            destination_registers: IndexMap::new(),
            output_registers: IndexMap::new(),
        }
    }

    /// Returns `true` if the given register exists.
    pub fn contains(&self, register: &Register<N>) -> bool {
        // The input and destination registers represent the full set of registers.
        // The output registers represent the subset of registers that are returned by the function.
        self.input_registers.contains_key(&register.locator())
            || self.destination_registers.contains_key(&register.locator())
    }

    /// Returns `true` if the given register corresponds to an input register.
    pub fn is_input(&self, register: &Register<N>) -> bool {
        self.input_registers.contains_key(&register.locator())
    }

    /// Returns `true` if the given register corresponds to an output register.
    pub fn is_output(&self, register: &Register<N>) -> bool {
        self.output_registers.contains_key(register)
    }

    /// Returns an iterator over all input registers.
    pub fn to_inputs(&self) -> impl '_ + Iterator<Item = (Register<N>, ValueType<N>)> {
        self.input_registers.iter().map(|(locator, value_type)| (Register::Locator(*locator), *value_type))
    }

    /// Returns an iterator over all output registers.
    pub fn to_outputs(&self) -> impl '_ + Iterator<Item = (&Register<N>, &ValueType<N>)> {
        self.output_registers.iter()
    }

    /// Inserts the given input register and type into the registers.
    /// Note: The given input register must be a `Register::Locator`.
    pub fn add_input(&mut self, register: Register<N>, value_type: ValueType<N>) -> Result<()> {
        // Ensure there are no destination or output registers set yet.
        ensure!(
            self.destination_registers.is_empty(),
            "Cannot add input register after destination registers have been set."
        );
        ensure!(self.output_registers.is_empty(), "Cannot add input register after output registers have been set.");

        // Check the input register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                ensure!(self.input_registers.len() as u64 == locator, "Register '{register}' is out of order");
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
        // Insert the input register and type.
        match self.input_registers.insert(register.locator(), value_type) {
            // If the register already exists, throw an error.
            Some(..) => bail!("Input '{register}' already exists"),
            // If the register does not exist, return success.
            None => Ok(()),
        }
    }

    /// Inserts the given destination register and type into the registers.
    /// Note: The given destination register must be a `Register::Locator`.
    pub fn add_destination(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Check the destination register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                let expected_locator = (self.input_registers.len() as u64) + self.destination_registers.len() as u64;
                ensure!(expected_locator == locator, "Register '{register}' is out of order");
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
        // Insert the destination register and type.
        match self.destination_registers.insert(register.locator(), register_type) {
            // If the register already exists, throw an error.
            Some(..) => bail!("Destination '{register}' already exists"),
            // If the register does not exist, return success.
            None => Ok(()),
        }
    }

    /// Inserts the given register as an output register with the associated value type.
    pub fn add_output(&mut self, register: &Register<N>, value_type: ValueType<N>) -> Result<()> {
        // Ensure the given register already exists.
        ensure!(self.contains(register), "Register '{register}' does not exist");
        // Insert the output register and type.
        match self.output_registers.insert(register.clone(), value_type) {
            // If the register already exists, throw an error.
            Some(..) => bail!("Register '{register}' already exists"),
            // If the register does not exist, return success.
            None => Ok(()),
        }
    }

    /// Returns the plaintext type of the given register.
    pub fn get_type(&self, program: &Program<N>, register: &Register<N>) -> Result<RegisterType<N>> {
        // Determine if the register is an input register.
        // Initialize a tracker for the register type.
        let mut register_type = if self.is_input(register) {
            // Retrieve the input value type as a register type.
            match self.input_registers.get(&register.locator()).ok_or_else(|| anyhow!("'{register}' does not exist"))? {
                ValueType::Constant(plaintext_type)
                | ValueType::Public(plaintext_type)
                | ValueType::Private(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                ValueType::Record(record_name) => RegisterType::Record(*record_name),
            }
        } else {
            // Retrieve the destination register type.
            *self
                .destination_registers
                .get(&register.locator())
                .ok_or_else(|| anyhow!("'{register}' does not exist"))?
        };

        match &register {
            // If the register is a locator, then output the register type.
            Register::Locator(..) => Ok(register_type),
            // If the register is a member, then traverse the member path to output the register type.
            Register::Member(_, path) => {
                // Ensure the member path is valid.
                ensure!(path.len() > 0, "Register '{register}' references no members.");

                // Traverse the member path to find the register type.
                for member_name in path.iter() {
                    match &register_type {
                        // Ensure the plaintext type is not a literal, as the register references a member.
                        RegisterType::Plaintext(PlaintextType::Literal(..)) => {
                            bail!("Register '{register}' references a literal.")
                        }
                        // Traverse the member path to output the register type.
                        RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                            // Retrieve the interface.
                            match program.get_interface(&interface_name) {
                                // Retrieve the member type from the interface.
                                Ok(interface) => match interface.members().get(member_name) {
                                    // Update the member type.
                                    Some(plaintext_type) => register_type = RegisterType::Plaintext(*plaintext_type),
                                    None => {
                                        bail!("Member '{member_name}' does not exist in '{interface_name}'")
                                    }
                                },
                                Err(..) => {
                                    bail!("'{register}' references a missing interface '{interface_name}'.")
                                }
                            }
                        }
                        RegisterType::Record(record_name) => {
                            // Retrieve the record.
                            match program.get_record(&record_name) {
                                // Retrieve the member type from the record.
                                Ok(record_type) => match record_type.entries().get(member_name) {
                                    // Update the member type.
                                    Some(value_type) => {
                                        register_type = match value_type {
                                            ValueType::Constant(plaintext_type)
                                            | ValueType::Public(plaintext_type)
                                            | ValueType::Private(plaintext_type) => {
                                                RegisterType::Plaintext(*plaintext_type)
                                            }
                                            ValueType::Record(record_name) => RegisterType::Record(*record_name),
                                        }
                                    }
                                    None => {
                                        bail!("Member '{member_name}' does not exist in '{record_name}'")
                                    }
                                },
                                Err(..) => {
                                    bail!("'{register}' references a missing record '{record_name}'.")
                                }
                            }
                        }
                    }
                }
                // Output the member type.
                Ok(register_type)
            }
        }
    }
}
