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

impl<N: Network> Stack<N> {
    /// Loads the literal of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub(crate) fn load_literal(&self, operand: &Operand<N>) -> Result<Literal<N>> {
        match self.load(operand)? {
            StackValue::Plaintext(Plaintext::Literal(literal, ..)) => Ok(literal),
            StackValue::Plaintext(Plaintext::Interface(..)) => bail!("Operand must be a literal"),
            StackValue::Record(..) => bail!("Operand must be a literal"),
        }
    }

    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub(crate) fn load(&self, operand: &Operand<N>) -> Result<StackValue<N>> {
        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => return Ok(StackValue::Plaintext(Plaintext::from(literal))),
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
        };

        // Determine if the register is an input register.
        let is_input_register = self.input_registers.contains_key(&register.locator());

        // Retrieve the stack value.
        let stack_value = match is_input_register {
            // Retrieve the input value.
            true => self
                .input_registers
                .get(&register.locator())
                .ok_or_else(|| anyhow!("'{register}' does not exist"))?
                .clone(),
            // Retrieve the destination register value.
            false => self
                .destination_registers
                .get(&register.locator())
                .ok_or_else(|| anyhow!("'{register}' does not exist"))?
                .clone(),
        };

        // Return the value for the given register or register member.
        match register {
            // If the register is a locator, then return the stack value.
            Register::Locator(..) => Ok(stack_value),
            // If the register is a register member, then load the specific stack value.
            Register::Member(_, ref path) => {
                match stack_value {
                    // Retrieve the plaintext member from the path.
                    StackValue::Plaintext(plaintext) => Ok(StackValue::Plaintext(plaintext.find(path)?)),
                    // Retrieve the record entry from the path.
                    StackValue::Record(record) => match record.find(path)? {
                        Entry::Constant(plaintext) | Entry::Public(plaintext) | Entry::Private(plaintext) => {
                            Ok(StackValue::Plaintext(plaintext))
                        }
                    },
                }
            }
        }
    }
}
