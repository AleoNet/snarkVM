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

use crate::stack::{CallOperator, Closure, Function, Instruction, Opcode, Program, StackMatches, StackProgram};
use console::{
    network::prelude::*,
    program::{
        EntryType,
        Identifier,
        LiteralType,
        PlaintextType,
        RecordType,
        Register,
        RegisterType,
        Struct,
        ValueType,
    },
};
use snarkvm_synthesizer_program::{InstructionTrait, Operand};

use indexmap::IndexMap;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct RegisterTypes<N: Network> {
    /// The mapping of all input registers to their defined types.
    inputs: IndexMap<u64, RegisterType<N>>,
    /// The mapping of all destination registers to their defined types.
    destinations: IndexMap<u64, RegisterType<N>>,
}

impl<N: Network> RegisterTypes<N> {
    /// Initializes a new instance of `RegisterTypes` for the given closure.
    /// Checks that the given closure is well-formed for the given stack.
    #[inline]
    pub fn from_closure(stack: &(impl StackMatches<N> + StackProgram<N>), closure: &Closure<N>) -> Result<Self> {
        Self::initialize_closure_types(stack, closure)
    }

    /// Initializes a new instance of `RegisterTypes` for the given function.
    /// Checks that the given function is well-formed for the given stack.
    #[inline]
    pub fn from_function(stack: &(impl StackMatches<N> + StackProgram<N>), function: &Function<N>) -> Result<Self> {
        Self::initialize_function_types(stack, function)
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

    /// Returns the register type of the given operand.
    pub fn get_type_from_operand(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        operand: &Operand<N>,
    ) -> Result<RegisterType<N>> {
        Ok(match operand {
            Operand::Literal(literal) => RegisterType::Plaintext(PlaintextType::from(literal.to_type())),
            Operand::Register(register) => self.get_type(stack, register)?,
            Operand::ProgramID(_) => RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address)),
            Operand::Caller => RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address)),
            Operand::BlockHeight => bail!("'block.height' is not a valid operand in a non-finalize context."),
        })
    }

    /// Returns the register type of the given register.
    pub fn get_type(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        register: &Register<N>,
    ) -> Result<RegisterType<N>> {
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
                RegisterType::Plaintext(PlaintextType::Struct(struct_name)) => {
                    // Retrieve the member type from the struct.
                    match stack.program().get_struct(struct_name)?.members().get(path_name) {
                        // Update the member type.
                        Some(plaintext_type) => RegisterType::Plaintext(*plaintext_type),
                        None => bail!("'{path_name}' does not exist in struct '{struct_name}'"),
                    }
                }
                RegisterType::Record(record_name) => {
                    // Ensure the record type exists.
                    ensure!(stack.program().contains_record(record_name), "Record '{record_name}' does not exist");
                    // Retrieve the member type from the record.
                    if path_name == &Identifier::from_str("owner")? {
                        // If the member is the owner, then output the address type.
                        RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Address))
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
