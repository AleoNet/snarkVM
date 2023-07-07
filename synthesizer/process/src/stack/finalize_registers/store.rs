// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> RegistersStore<N> for FinalizeRegisters<N> {
    /// Assigns the given value to the given register, assuming the register is not already assigned.
    ///
    /// # Errors
    /// This method will halt if the given register is a register member.
    /// This method will halt if the given register is an input register.
    /// This method will halt if the register is already used.
    #[inline]
    fn store(
        &mut self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        register: &Register<N>,
        stack_value: Value<N>,
    ) -> Result<()> {
        // Ensure that the stack value is a plaintext value.
        let plaintext_value = match stack_value {
            Value::Plaintext(plaintext) => plaintext,
            Value::Record(_) => bail!("Cannot store a record in a finalize register"),
        };
        // Store the value to the register.
        match register {
            Register::Locator(locator) => {
                // Ensure the register assignments are monotonically increasing.
                let expected_locator = self.registers.len() as u64;
                ensure!(expected_locator == *locator, "Out-of-order write operation at '{register}'");
                // Ensure the register does not already exist.
                ensure!(!self.registers.contains_key(locator), "Cannot write to occupied register '{register}'");

                // Ensure the type of the register is valid.
                match self.finalize_types.get_type(stack, register) {
                    // Ensure the plaintext value matches the plaintext type.
                    Ok(plaintext_type) => stack.matches_plaintext(&plaintext_value, &plaintext_type)?,
                    // Ensure the register is defined.
                    Err(error) => bail!("Register '{register}' is missing a type definition: {error}"),
                };

                // Store the plaintext value.
                match self.registers.insert(*locator, plaintext_value) {
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
