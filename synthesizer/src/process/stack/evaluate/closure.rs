// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    /// Evaluates a program closure on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate_closure<A: circuit::Aleo<Network = N>>(
        &self,
        closure: &Closure<N>,
        inputs: &[Value<N>],
        call_stack: CallStack<N>,
        caller: Address<N>,
        tvk: Field<N>,
    ) -> Result<Vec<Value<N>>> {
        let timer = timer!("Stack::evaluate_closure");

        // Ensure the number of inputs matches the number of input statements.
        if closure.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", closure.inputs().len(), inputs.len())
        }

        // Initialize the registers.
        let mut registers = Registers::<N, A>::new(call_stack, self.get_register_types(closure.name())?.clone());
        // Set the transition caller.
        registers.set_caller(caller);
        // Set the transition view key.
        registers.set_tvk(tvk);
        lap!(timer, "Initialize the registers");

        // Store the inputs.
        closure.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            registers.store(self, register, input.clone())
        })?;
        lap!(timer, "Store the inputs");

        // Evaluate the instructions.
        for instruction in closure.instructions() {
            // If the evaluation fails, bail and return the error.
            if let Err(error) = instruction.evaluate(self, &mut registers) {
                bail!("Failed to evaluate instruction ({instruction}): {error}");
            }
        }
        lap!(timer, "Evaluate the instructions");

        // Load the outputs.
        let outputs = closure
            .outputs()
            .iter()
            .map(|output| {
                match output.operand() {
                    // If the operand is a literal, use the literal directly.
                    Operand::Literal(literal) => Ok(Value::Plaintext(Plaintext::from(literal))),
                    // If the operand is a register, retrieve the stack value from the register.
                    Operand::Register(register) => registers.load(self, &Operand::Register(register.clone())),
                    // If the operand is the program ID, convert the program ID into an address.
                    Operand::ProgramID(program_id) => {
                        Ok(Value::Plaintext(Plaintext::from(Literal::Address(program_id.to_address()?))))
                    }
                    // If the operand is the caller, retrieve the caller from the registers.
                    Operand::Caller => Ok(Value::Plaintext(Plaintext::from(Literal::Address(registers.caller()?)))),
                }
            })
            .collect();
        lap!(timer, "Load the outputs");

        finish!(timer);
        outputs
    }
}
