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

mod deploy;
mod evaluate;
mod execute;
mod matches;
mod sample;
mod synthesize;

use crate::{
    Authorization,
    CallOperator,
    Certificate,
    CircuitKeys,
    Closure,
    Deployment,
    Execution,
    Function,
    Instruction,
    Operand,
    Program,
    ProvingKey,
    RegisterTypes,
    Registers,
    Transition,
    VerifyingKey,
};
use console::{
    account::{Address, PrivateKey},
    network::prelude::*,
    program::{
        Balance,
        Entry,
        EntryType,
        Identifier,
        Literal,
        Locator,
        Owner,
        Plaintext,
        PlaintextType,
        ProgramID,
        Record,
        RecordType,
        RegisterType,
        Request,
        Response,
        Value,
        ValueType,
        U64,
    },
};

use indexmap::IndexMap;
use parking_lot::RwLock;
use std::sync::Arc;

pub type Assignments<N> = Arc<RwLock<Vec<circuit::Assignment<<N as Environment>::Field>>>>;

#[derive(Clone)]
pub enum CallStack<N: Network> {
    Authorize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    Synthesize(Vec<Request<N>>, PrivateKey<N>, Authorization<N>),
    CheckDeployment(Vec<Request<N>>, PrivateKey<N>, Assignments<N>),
    Evaluate,
    Execute(Authorization<N>, Arc<RwLock<Execution<N>>>),
}

impl<N: Network> CallStack<N> {
    /// Pushes the request to the stack.
    pub fn push(&mut self, request: Request<N>) -> Result<()> {
        match self {
            CallStack::Authorize(requests, ..) => requests.push(request),
            CallStack::Synthesize(requests, ..) => requests.push(request),
            CallStack::CheckDeployment(requests, ..) => requests.push(request),
            CallStack::Evaluate => (),
            CallStack::Execute(authorization, ..) => authorization.push(request),
        }
        Ok(())
    }

    /// Pops the request from the stack.
    pub fn pop(&mut self) -> Result<Request<N>> {
        match self {
            CallStack::Authorize(requests, ..)
            | CallStack::Synthesize(requests, ..)
            | CallStack::CheckDeployment(requests, ..) => {
                requests.pop().ok_or_else(|| anyhow!("No more requests on the stack"))
            }
            CallStack::Evaluate => bail!("No requests on the stack when in `evaluate` mode"),
            CallStack::Execute(authorization, ..) => authorization.next(),
        }
    }
}

#[derive(Clone)]
pub struct Stack<N: Network> {
    /// The program (record types, interfaces, functions).
    program: Program<N>,
    /// The mapping of external stacks as `(program ID, stack)`.
    external_stacks: IndexMap<ProgramID<N>, Stack<N>>,
    /// The mapping of closure and function names to their register types.
    program_types: IndexMap<Identifier<N>, RegisterTypes<N>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: CircuitKeys<N>,
}

impl<N: Network> Stack<N> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N>, circuit_keys: CircuitKeys<N>) -> Result<Self> {
        // TODO (howardwu): Process every closure and function before returning.
        Ok(Self { program, external_stacks: IndexMap::new(), program_types: IndexMap::new(), circuit_keys })
    }

    /// Adds a new external stack to the stack.
    #[inline]
    pub fn add_external_stack(&mut self, external_stack: Stack<N>) -> Result<()> {
        // Retrieve the program ID.
        let program_id = *external_stack.program_id();
        // Ensure the external stack is not already added.
        ensure!(!self.external_stacks.contains_key(&program_id), "Program '{program_id}' already exists");
        // Ensure the program exists in the main program imports.
        ensure!(self.program.contains_import(&program_id), "'{program_id}' does not exist in the main program imports");
        // Ensure the external stack is not for the main program.
        ensure!(self.program.id() != external_stack.program_id(), "External stack program cannot be the main program");
        // Add the external stack to the stack.
        self.external_stacks.insert(program_id, external_stack);
        // Return success.
        Ok(())
    }

    /// Adds the given closure name and register types to the stack.
    #[inline]
    pub fn add_closure_types(&mut self, name: &Identifier<N>, register_types: RegisterTypes<N>) -> Result<()> {
        // Ensure the closure name is not already added.
        ensure!(!self.program_types.contains_key(name), "Closure '{name}' already exists");
        // Add the closure name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Adds the given function name and register types to the stack.
    #[inline]
    pub fn add_function_types(&mut self, name: &Identifier<N>, register_types: RegisterTypes<N>) -> Result<()> {
        // Ensure the function name is not already added.
        ensure!(!self.program_types.contains_key(name), "Function '{name}' already exists");
        // Add the function name and register types to the stack.
        self.program_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the program ID.
    #[inline]
    pub const fn program_id(&self) -> &ProgramID<N> {
        self.program.id()
    }

    /// Returns `true` if the stack contains the external record.
    #[inline]
    pub fn contains_external_record(&self, locator: &Locator<N>) -> bool {
        // Retrieve the external program.
        match self.get_external_program(locator.program_id()) {
            // Return `true` if the external record exists.
            Ok(external_program) => external_program.contains_record(locator.resource()),
            // Return `false` otherwise.
            Err(_) => false,
        }
    }

    /// Returns the external stack for the given program ID.
    #[inline]
    pub fn get_external_stack(&self, program_id: &ProgramID<N>) -> Result<&Stack<N>> {
        // Retrieve the external stack.
        self.external_stacks.get(program_id).ok_or_else(|| anyhow!("External program '{program_id}' does not exist."))
    }

    /// Returns the external program for the given program ID.
    #[inline]
    pub fn get_external_program(&self, program_id: &ProgramID<N>) -> Result<&Program<N>> {
        match self.program.id() == program_id {
            true => bail!("Attempted to get the main program '{}' as an external program", self.program.id()),
            // Retrieve the external stack, and return the external program.
            false => Ok(self.get_external_stack(program_id)?.program()),
        }
    }

    /// Returns `true` if the stack contains the external record.
    #[inline]
    pub fn get_external_record(&self, locator: &Locator<N>) -> Result<RecordType<N>> {
        // Retrieve the external program.
        let external_program = self.get_external_program(locator.program_id())?;
        // Return the external record, if it exists.
        external_program.get_record(locator.resource())
    }

    /// Returns the function with the given function name.
    pub fn get_function(&self, function_name: &Identifier<N>) -> Result<Function<N>> {
        self.program.get_function(function_name)
    }

    /// Returns the expected number of calls for the given function name.
    #[inline]
    pub fn get_number_of_calls(&self, function_name: &Identifier<N>) -> Result<usize> {
        // Retrieve the function.
        let function = self.get_function(function_name)?;
        // Determine the number of calls for this function (including the function itself).
        let mut num_calls = 1;
        for instruction in function.instructions() {
            if let Instruction::Call(call) = instruction {
                // Determine if this is a function call.
                if call.is_function_call(self)? {
                    // Increment by the number of calls.
                    num_calls += match call.operator() {
                        CallOperator::Locator(locator) => {
                            self.get_external_stack(locator.program_id())?.get_number_of_calls(locator.resource())?
                        }
                        CallOperator::Resource(resource) => self.get_number_of_calls(resource)?,
                    };
                }
            }
        }
        Ok(num_calls)
    }

    /// Returns the register types for the given closure or function name.
    #[inline]
    pub fn get_register_types(&self, name: &Identifier<N>) -> Result<&RegisterTypes<N>> {
        // Retrieve the register types.
        self.program_types.get(name).ok_or_else(|| anyhow!("Register types for '{name}' does not exist"))
    }

    /// Returns the proving key for the given function name.
    #[inline]
    pub fn get_proving_key(&self, function_name: &Identifier<N>) -> Result<ProvingKey<N>> {
        // Return the proving key, if it exists.
        self.circuit_keys.get_proving_key(self.program_id(), function_name)
    }

    /// Returns the verifying key for the given function name.
    #[inline]
    pub fn get_verifying_key(&self, function_name: &Identifier<N>) -> Result<VerifyingKey<N>> {
        // Return the verifying key, if it exists.
        self.circuit_keys.get_verifying_key(self.program_id(), function_name)
    }
}

impl<N: Network> PartialEq for Stack<N> {
    fn eq(&self, other: &Self) -> bool {
        self.program == other.program
            && self.external_stacks == other.external_stacks
            && self.program_types == other.program_types
    }
}

impl<N: Network> Eq for Stack<N> {}
