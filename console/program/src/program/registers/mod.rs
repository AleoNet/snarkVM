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

use crate::{PlaintextType, Program, Register, ValueType};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum RegisterType<N: Network> {
    /// An input register type contains a plaintext type with visibility.
    Input(ValueType<N>),
    /// A destination register type contains a plaintext type from an instruction.
    Destination(PlaintextType<N>),
}

#[derive(Clone, PartialEq, Eq)]
pub struct RegisterTypes<N: Network> {
    /// The mapping of all registers to their defined types.
    register_types: IndexMap<u64, RegisterType<N>>,
}

impl<N: Network> RegisterTypes<N> {
    /// Initializes a new instance of `RegisterTypes`.
    pub fn new() -> Self {
        Self { register_types: IndexMap::new() }
    }

    /// Returns `true` if the given register exists.
    pub fn contains(&self, register: &Register<N>) -> bool {
        self.register_types.contains_key(&register.locator())
    }

    /// Returns `true` if the given register corresponds to an input register.
    pub fn is_input(&self, register: &Register<N>) -> bool {
        self.register_types
            .get(&register.locator())
            .map(|register_type| matches!(*register_type, RegisterType::Input(..)))
            .unwrap_or(false)
    }

    /// Returns an iterator over all input registers.
    pub fn to_inputs(&self) -> impl '_ + Iterator<Item = (Register<N>, RegisterType<N>)> {
        self.register_types
            .iter()
            .filter(|(_, register_type)| matches!(*register_type, RegisterType::Input(..)))
            .map(|(locator, register_type)| (Register::Locator(*locator), *register_type))
    }

    /// Inserts the given register and type into the registers.
    /// Note: The given register must be a `Register::Locator`.
    pub fn insert(&mut self, register: Register<N>, register_type: RegisterType<N>) -> Result<()> {
        // Check the register.
        match register {
            Register::Locator(locator) => {
                // Ensure the registers are monotonically increasing.
                ensure!(self.register_types.len() as u64 == locator, "Register '{register}' is out of order");
            }
            // Ensure the register is a locator, and not a member.
            Register::Member(..) => bail!("Register '{register}' must be a locator."),
        }
        // Insert the register and type.
        match self.register_types.insert(register.locator(), register_type) {
            // If the register already exists, throw an error.
            Some(..) => bail!("Register '{register}' already exists"),
            // If the register does not exist, return success.
            None => Ok(()),
        }
    }

    /// Returns the plaintext type of the given register.
    pub fn get_type(&self, program: &Program<N>, register: &Register<N>) -> Result<PlaintextType<N>> {
        // Retrieve the (starting) plaintext type.
        let plaintext_type = match self.register_types.get(&register.locator()) {
            // Retrieve the plaintext type from the value type.
            Some(RegisterType::Input(value_type)) => value_type.to_plaintext_type(),
            // Retrieve the plaintext type.
            Some(RegisterType::Destination(plaintext_type)) => *plaintext_type,
            // Ensure the register is defined.
            None => bail!("Register '{register}' does not exist"),
        };

        match &register {
            // If the register is a locator, then output the register type.
            Register::Locator(..) => Ok(plaintext_type),
            // If the register is a member, then traverse the member path to output the register type.
            Register::Member(_, path) => {
                // Ensure the member path is valid.
                ensure!(path.len() > 0, "Register '{register}' references no members.");

                // Initialize a tracker for the plaintext type.
                let mut plaintext_type = plaintext_type;
                // Traverse the member path to find the register type.
                for member_name in path.iter() {
                    match plaintext_type {
                        // Ensure the plaintext type is not a literal, as the register references a member.
                        PlaintextType::Literal(..) => bail!("Register '{register}' references a literal."),
                        // Traverse the member path to output the register type.
                        PlaintextType::Interface(interface_name) => {
                            // Retrieve the interface.
                            match program.get_interface(&interface_name) {
                                // Retrieve the member type from the interface.
                                Ok(interface) => match interface.members().get(member_name) {
                                    // Update the plaintext type.
                                    Some(member_type) => plaintext_type = *member_type,
                                    None => {
                                        bail!("Member '{member_name}' does not exist in '{interface_name}'")
                                    }
                                },
                                Err(..) => {
                                    bail!("'{register}' references a missing interface '{interface_name}'.")
                                }
                            }
                        }
                    }
                }
                // Output the member type.
                Ok(plaintext_type)
            }
        }
    }
}
