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

use super::*;

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Assigns the given literal to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store_literal(&mut self, register: &Register<N>, literal: Literal<N>) -> Result<()> {
        self.store(register, Value::Plaintext(Plaintext::from(literal)))
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store(&mut self, register: &Register<N>, stack_value: Value<N>) -> Result<()> {
        match register {
            Register::Locator(locator) => {
                // Ensure the register assignments are monotonically increasing.
                let expected_locator = self.console_registers.len() as u64;
                ensure!(expected_locator == *locator, "Out-of-order write operation at '{register}'");
                // Ensure the register does not already exist.
                ensure!(
                    !self.console_registers.contains_key(locator),
                    "Cannot write to occupied register '{register}'"
                );

                // Ensure the register type is valid.
                match self.register_types.get_type(self, register) {
                    // Ensure the stack value matches the register type.
                    Ok(register_type) => self.matches_register_type(&stack_value, &register_type)?,
                    // Ensure the register is defined.
                    Err(error) => bail!("Register '{register}' is missing a type definition: {error}"),
                };

                // Store the stack value.
                match self.console_registers.insert(*locator, stack_value) {
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
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Assigns the given literal to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store_literal_circuit(&mut self, register: &Register<N>, literal: circuit::Literal<A>) -> Result<()> {
        self.store_circuit(register, circuit::Value::Plaintext(circuit::Plaintext::from(literal)))
    }

    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    pub fn store_circuit(&mut self, register: &Register<N>, circuit_value: circuit::Value<A>) -> Result<()> {
        match register {
            Register::Locator(locator) => {
                // Ensure the register assignments are monotonically increasing.
                let expected_locator = self.circuit_registers.len() as u64;
                ensure!(expected_locator == *locator, "Out-of-order write operation at '{register}'");
                // Ensure the register does not already exist.
                ensure!(
                    !self.circuit_registers.contains_key(locator),
                    "Cannot write to occupied register '{register}'"
                );

                // Ensure the register type is valid.
                match self.register_types.get_type(self, register) {
                    // Ensure the stack value matches the register type.
                    Ok(register_type) => {
                        self.matches_register_type(&circuit::Eject::eject_value(&circuit_value), &register_type)?
                    }
                    // Ensure the register is defined.
                    Err(error) => bail!("Register '{register}' is missing a type definition: {error}"),
                };

                // Store the stack value.
                match self.circuit_registers.insert(*locator, circuit_value) {
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
}
