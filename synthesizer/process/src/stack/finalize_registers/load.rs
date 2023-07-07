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

impl<N: Network> RegistersLoad<N> for FinalizeRegisters<N> {
    /// Loads the value of a given operand from the registers.
    ///
    /// # Errors
    /// This method will halt if the register locator is not found.
    /// In the case of register members, this method will halt if the member is not found.
    #[inline]
    fn load(&self, stack: &(impl StackMatches<N> + StackProgram<N>), operand: &Operand<N>) -> Result<Value<N>> {
        // Retrieve the register.
        let register = match operand {
            // If the operand is a literal, return the literal.
            Operand::Literal(literal) => return Ok(Value::Plaintext(Plaintext::from(literal))),
            // If the operand is a register, load the value from the register.
            Operand::Register(register) => register,
            // If the operand is the program ID, load the program address.
            Operand::ProgramID(program_id) => {
                return Ok(Value::Plaintext(Plaintext::from(Literal::Address(program_id.to_address()?))));
            }
            // If the operand is the caller, throw an error.
            Operand::Caller => bail!("Forbidden operation: Cannot use 'self.caller' in 'finalize'"),
            // If the operand is the block height, load the block height.
            Operand::BlockHeight => {
                return Ok(Value::Plaintext(Plaintext::from(Literal::U32(U32::new(self.state.block_height())))));
            }
        };

        // Retrieve the plaintext value.
        let plaintext_value =
            self.registers.get(&register.locator()).ok_or_else(|| anyhow!("'{register}' does not exist"))?;

        // Return the value for the given register or register member.
        let plaintext_value = match register {
            // If the register is a locator, then return the plaintext value.
            Register::Locator(..) => plaintext_value.clone(),
            // If the register is a register member, then load the specific plaintext value.
            Register::Member(_, ref path) => plaintext_value.find(path)?,
        };

        // Retrieve the type of the register.
        match self.finalize_types.get_type(stack, register) {
            // Ensure the plaintext value matches the register type.
            Ok(plaintext_type) => stack.matches_plaintext(&plaintext_value, &plaintext_type)?,
            // Ensure the register is defined.
            Err(error) => bail!("Register '{register}' is not a member of the function: {error}"),
        };

        Ok(Value::Plaintext(plaintext_value))
    }
}
