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

use crate::{function::instruction::Operand, Literal, Plaintext, Register};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

/// The registers contains a mapping of the registers to their corresponding values in a function.
#[derive(Clone, Default)]
pub struct Registers<N: Network> {
    /// The mapping of registers to their values.
    registers: IndexMap<u64, Option<Plaintext<N>>>,
    /// The number of registers assigned in the function.
    num_assigned: u64,
}

impl<N: Network> Registers<N> {
    /// Initializes a new instance of the registers.
    #[inline]
    pub fn new() -> Self {
        Self { registers: IndexMap::new(), num_assigned: 0 }
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the register was previously stored.
    #[inline]
    pub fn store(&mut self, register: &Register<N>, value: Plaintext<N>) -> Result<()> {
        // Ensure the register assignments are monotonically increasing.
        ensure!(
            self.num_assigned == register.locator(),
            "Expected \'{}\', found \'{register}\'",
            Register::<N>::Locator(self.num_assigned)
        );

        // Store the value in the register.
        let previous = match register {
            // Store the value for a register.
            Register::Locator(locator) => self.registers.insert(*locator, Some(value)),
            // Store the value for a register member.
            Register::Member(..) => bail!("Cannot store directly to \'{register}\'"),
        };

        // Ensure the register has not been previously stored.
        match previous {
            // Halt if the register was previously stored.
            Some(Some(..)) => bail!("Register \'{register}\' was previously assigned"),
            // Increment the number of assigned registers.
            Some(None) => self.num_assigned += 1,
            // Halt if the register was not previously defined.
            None => bail!("Register \'{register}\' was not defined before assignment"),
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

        // Retrieve the value from the register.
        let value = match self.registers.get(&register.locator()) {
            // Return the value if it exists.
            Some(Some(value)) => (*value).clone(),
            // Halts if the value does not exist.
            Some(None) | None => bail!("Failed to locate register \'{register}\'"),
        };

        // Return the value for the given register or register member.
        match register {
            // If the register is a locator, then return the value.
            Register::Locator(..) => Ok(value),
            // If the register is a register member, then load the specific value.
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

    /// Clears the registers of their assignments, preserving the register definitions.
    /// This allows a function to be re-executed without having to re-define the registers.
    #[inline]
    pub fn clear_assignments(&mut self) {
        // Clear the assignments in each register.
        self.registers.values_mut().for_each(|value| *value = None);
    }
}
