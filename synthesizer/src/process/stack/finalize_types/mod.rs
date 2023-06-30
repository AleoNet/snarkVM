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

mod initialize;
mod matches;

use crate::stack::{Command, Finalize, Instruction, Opcode, Program, StackMatches, StackProgram};
use console::{
    network::prelude::*,
    program::{Identifier, LiteralType, PlaintextType, Register, RegisterType, Struct},
};
use snarkvm_synthesizer_program::{InstructionTrait, Operand};

use indexmap::IndexMap;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct FinalizeTypes<N: Network> {
    /// The mapping of all input registers to their defined types.
    /// Note that in a finalize context, all registers are plaintext types.
    inputs: IndexMap<u64, PlaintextType<N>>,
    /// The mapping of all destination registers to their defined types.
    /// Note that in a finalize context, all registers are plaintext types.
    destinations: IndexMap<u64, PlaintextType<N>>,
}

impl<N: Network> FinalizeTypes<N> {
    /// Initializes a new instance of `FinalizeTypes` for the given finalize.
    /// Checks that the given finalize is well-formed for the given stack.
    #[inline]
    pub fn from_finalize(stack: &(impl StackMatches<N> + StackProgram<N>), finalize: &Finalize<N>) -> Result<Self> {
        Self::initialize_finalize_types(stack, finalize)
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

    /// Returns the type of the given operand.
    pub fn get_type_from_operand(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        operand: &Operand<N>,
    ) -> Result<PlaintextType<N>> {
        Ok(match operand {
            Operand::Literal(literal) => PlaintextType::from(literal.to_type()),
            Operand::Register(register) => self.get_type(stack, register)?,
            Operand::ProgramID(_) => PlaintextType::Literal(LiteralType::Address),
            Operand::Caller => bail!("'self.caller' is not a valid operand in a finalize context."),
            Operand::BlockHeight => PlaintextType::Literal(LiteralType::U32),
        })
    }

    /// Returns the type of the given register.
    pub fn get_type(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        register: &Register<N>,
    ) -> Result<PlaintextType<N>> {
        // Initialize a tracker for the type of the register.
        let mut plaintext_type = if self.is_input(register) {
            // Retrieve the input value type as a register type.
            *self.inputs.get(&register.locator()).ok_or_else(|| anyhow!("Register '{register}' does not exist"))?
        } else {
            // Retrieve the destination register type.
            *self
                .destinations
                .get(&register.locator())
                .ok_or_else(|| anyhow!("Register '{register}' does not exist"))?
        };

        // Retrieve the member path if the register is a member. Otherwise, return the type.
        let path = match &register {
            // If the register is a locator, then output the register type.
            Register::Locator(..) => return Ok(plaintext_type),
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
            plaintext_type = match &plaintext_type {
                // Ensure the plaintext type is not a literal, as the register references a member.
                PlaintextType::Literal(..) => bail!("'{register}' references a literal."),
                // Traverse the member path to output the register type.
                PlaintextType::Struct(struct_name) => {
                    // Retrieve the member type from the struct.
                    match stack.program().get_struct(struct_name)?.members().get(path_name) {
                        // Update the member type.
                        Some(plaintext_type) => *plaintext_type,
                        None => bail!("'{path_name}' does not exist in struct '{struct_name}'"),
                    }
                }
            }
        }
        // Output the member type.
        Ok(plaintext_type)
    }
}
