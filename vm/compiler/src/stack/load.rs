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
    /// Loads the literal of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load_literal(&self, operand: &Operand<N>) -> Result<Literal<N>> {
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
    pub fn load(&self, operand: &Operand<N>) -> Result<StackValue<N>> {
        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => return Ok(StackValue::Plaintext(Plaintext::from(literal))),
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
        };

        // Retrieve the stack value.
        let stack_value =
            self.console_registers.get(&register.locator()).ok_or_else(|| anyhow!("'{register}' does not exist"))?;

        // Return the value for the given register or register member.
        let stack_value = match register {
            // If the register is a locator, then return the stack value.
            Register::Locator(..) => stack_value.clone(),
            // If the register is a register member, then load the specific stack value.
            Register::Member(_, ref path) => {
                match stack_value {
                    // Retrieve the plaintext member from the path.
                    StackValue::Plaintext(plaintext) => StackValue::Plaintext(plaintext.find(path)?),
                    // Retrieve the record entry from the path.
                    StackValue::Record(record) => match record.find(path)? {
                        Entry::Constant(plaintext) | Entry::Public(plaintext) | Entry::Private(plaintext) => {
                            StackValue::Plaintext(plaintext)
                        }
                    },
                }
            }
        };

        // Retrieve the register type.
        match self.register_types.get_type(&self.program, register) {
            // Ensure the stack value matches the register type.
            Ok(register_type) => self.program.matches_register(&stack_value, &register_type)?,
            // Ensure the register is defined.
            Err(error) => bail!("Register '{register}' is not a member of the function: {error}"),
        };

        Ok(stack_value)
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Loads the literal circuit of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the given operand is not a literal.
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load_literal_circuit(&self, operand: &Operand<N>) -> Result<circuit::program::Literal<A>> {
        match self.load_circuit(operand)? {
            circuit::CircuitValue::Plaintext(circuit::Plaintext::Literal(literal, ..)) => Ok(literal),
            circuit::CircuitValue::Plaintext(circuit::Plaintext::Interface(..)) => bail!("Operand must be a literal"),
            circuit::CircuitValue::Record(..) => bail!("Operand must be a literal"),
        }
    }

    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    pub fn load_circuit(&self, operand: &Operand<N>) -> Result<circuit::CircuitValue<A>> {
        use circuit::Inject;

        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => {
                return Ok(circuit::CircuitValue::Plaintext(circuit::Plaintext::from(circuit::Literal::constant(
                    literal.clone(),
                ))));
            }
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
        };

        // Retrieve the circuit value.
        let circuit_value =
            self.circuit_registers.get(&register.locator()).ok_or_else(|| anyhow!("'{register}' does not exist"))?;

        // Return the value for the given register or register member.
        let circuit_value = match register {
            // If the register is a locator, then return the stack value.
            Register::Locator(..) => circuit_value.clone(),
            // If the register is a register member, then load the specific stack value.
            Register::Member(_, ref path) => {
                // Inject the path.
                let path = path.iter().map(|member| circuit::Identifier::constant(*member)).collect::<Vec<_>>();

                match circuit_value {
                    // Retrieve the plaintext member from the path.
                    circuit::CircuitValue::Plaintext(plaintext) => {
                        circuit::CircuitValue::Plaintext(plaintext.find(&path)?)
                    }
                    // Retrieve the record entry from the path.
                    circuit::CircuitValue::Record(record) => match record.find(&path)? {
                        circuit::Entry::Constant(plaintext)
                        | circuit::Entry::Public(plaintext)
                        | circuit::Entry::Private(plaintext) => circuit::CircuitValue::Plaintext(plaintext),
                    },
                }
            }
        };

        // Retrieve the register type.
        match self.register_types.get_type(&self.program, register) {
            // Ensure the stack value matches the register type.
            Ok(register_type) => {
                self.program.matches_register(&circuit::Eject::eject_value(&circuit_value), &register_type)?
            }
            // Ensure the register is defined.
            Err(error) => bail!("Register '{register}' is not a member of the function: {error}"),
        };

        Ok(circuit_value)
    }
}
