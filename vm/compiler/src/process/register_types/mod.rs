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

use crate::{Operand, Stack};
use console::{
    network::prelude::*,
    program::{EntryType, Identifier, Interface, LiteralType, PlaintextType, RecordType, Register, RegisterType},
};

use indexmap::IndexMap;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct RegisterTypes<N: Network> {
    /// The mapping of all input registers to their defined types.
    inputs: IndexMap<u64, RegisterType<N>>,
    /// The mapping of all destination registers to their defined types.
    destinations: IndexMap<u64, RegisterType<N>>,
}

impl<N: Network> RegisterTypes<N> {
    /// Initializes a new instance of `RegisterTypes`.
    pub fn new() -> Self {
        Self { inputs: IndexMap::new(), destinations: IndexMap::new() }
    }

    /// Returns `true` if the given register exists.
    pub fn contains(&self, register: &Register<N>) -> bool {
        // Retrieve the register locator.
        let locator = &register.locator();
        // The input and destination registers represent the full set of registers.
        // The output registers represent a subset of registers that are returned by the function.
        self.inputs.contains_key(locator) || self.destinations.contains_key(locator)
    }

    /// Returns `true` if the given register corresponds to an input register.
    pub fn is_input(&self, register: &Register<N>) -> bool {
        self.inputs.contains_key(&register.locator())
    }

    /// Inserts the given input register and type into the registers.
    /// Note: The given input register must be a `Register::Locator`.
    pub fn add_input(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Ensure there are no destination registers set yet.
        ensure!(self.destinations.is_empty(), "Cannot add input registers after destination registers.");

        // Check the input register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                ensure!(self.inputs.len() as u64 == locator, "Register '{register}' is out of order");

                // Insert the input register and type.
                match self.inputs.insert(locator, register_type) {
                    // If the register already exists, throw an error.
                    Some(..) => bail!("Input '{register}' already exists"),
                    // If the register does not exist, return success.
                    None => Ok(()),
                }
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
    }

    /// Inserts the given destination register and type into the registers.
    /// Note: The given destination register must be a `Register::Locator`.
    pub fn add_destination(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Check the destination register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                let expected_locator = (self.inputs.len() as u64) + self.destinations.len() as u64;
                ensure!(expected_locator == locator, "Register '{register}' is out of order");

                // Insert the destination register and type.
                match self.destinations.insert(locator, register_type) {
                    // If the register already exists, throw an error.
                    Some(..) => bail!("Destination '{register}' already exists"),
                    // If the register does not exist, return success.
                    None => Ok(()),
                }
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
    }

    /// Returns the register type of the given register.
    pub fn get_type(&self, stack: &Stack<N>, register: &Register<N>) -> Result<RegisterType<N>> {
        // Initialize a tracker for the register type.
        let mut register_type = if self.is_input(register) {
            // Retrieve the input value type as a register type.
            *self.inputs.get(&register.locator()).ok_or_else(|| anyhow!("Register '{register}' does not exist"))?
        } else {
            // Retrieve the destination register type.
            *self
                .destinations
                .get(&register.locator())
                .ok_or_else(|| anyhow!("Register '{register}' does not exist"))?
        };

        // Retrieve the member path if the register is a member. Otherwise, return the register type.
        let path = match &register {
            // If the register is a locator, then output the register type.
            Register::Locator(..) => return Ok(register_type),
            // If the register is a member, then traverse the member path to output the register type.
            Register::Member(_, path) => {
                // Ensure the member path is valid.
                ensure!(!path.is_empty(), "Register '{register}' references no members.");
                // Output the member path.
                path
            }
        };

        // Traverse the member path to find the register type.
        for path_name in path.iter() {
            // Update the register type at each step.
            register_type = match &register_type {
                // Ensure the plaintext type is not a literal, as the register references a member.
                RegisterType::Plaintext(PlaintextType::Literal(..)) => bail!("'{register}' references a literal."),
                // Traverse the member path to output the register type.
                RegisterType::Plaintext(PlaintextType::Interface(interface_name)) => {
                    // Retrieve the member type from the interface.
                    match stack.program().get_interface(interface_name)?.members().get(path_name) {
                        // Update the member type.
                        Some(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                        None => bail!("'{path_name}' does not exist in interface '{interface_name}'"),
                    }
                }
                RegisterType::Record(record_name) => {
                    // Ensure the record type exists.
                    ensure!(stack.program().contains_record(record_name), "Record '{record_name}' does not exist");
                    // Retrieve the member type from the record.
                    if path_name == &Identifier::from_str("owner")? {
                        // If the member is the owner, then output the address type.
                        RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address))
                    } else if path_name == &Identifier::from_str("gates")? {
                        // If the member is the gates, then output the u64 type.
                        RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U64))
                    } else {
                        // Retrieve the entry type from the record.
                        match stack.program().get_record(record_name)?.entries().get(path_name) {
                            // Update the entry type.
                            Some(entry_type) => match entry_type {
                                EntryType::Constant(plaintext_type)
                                | EntryType::Public(plaintext_type)
                                | EntryType::Private(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                            },
                            None => bail!("'{path_name}' does not exist in record '{record_name}'"),
                        }
                    }
                }
                RegisterType::ExternalRecord(locator) => {
                    // Ensure the external record type exists.
                    ensure!(stack.contains_external_record(locator), "External record '{locator}' does not exist");
                    // Retrieve the member type from the external record.
                    if path_name == &Identifier::from_str("owner")? {
                        // If the member is the owner, then output the address type.
                        RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address))
                    } else if path_name == &Identifier::from_str("gates")? {
                        // If the member is the gates, then output the u64 type.
                        RegisterType::Plaintext(PlaintextType::Literal(LiteralType::U64))
                    } else {
                        // Retrieve the entry type from the external record.
                        match stack.get_external_record(locator)?.entries().get(path_name) {
                            // Update the entry type.
                            Some(entry_type) => match entry_type {
                                EntryType::Constant(plaintext_type)
                                | EntryType::Public(plaintext_type)
                                | EntryType::Private(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                            },
                            None => bail!("'{path_name}' does not exist in external record '{locator}'"),
                        }
                    }
                }
            }
        }
        // Output the member type.
        Ok(register_type)
    }
}
