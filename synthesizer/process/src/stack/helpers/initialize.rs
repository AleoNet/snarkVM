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

impl<N: Network> Stack<N> {
    /// Initializes a new stack, given the process and program.
    #[inline]
    pub(crate) fn initialize(process: &Process<N>, program: &Program<N>) -> Result<Self> {
        // Construct the stack for the program.
        let mut stack = Self {
            program: program.clone(),
            external_stacks: Default::default(),
            register_types: Default::default(),
            finalize_types: Default::default(),
            universal_srs: process.universal_srs().clone(),
            proving_keys: Default::default(),
            verifying_keys: Default::default(),
        };

        // Add all of the imports into the stack.
        for import in program.imports().keys() {
            // Ensure the program imports all exist in the process already.
            if !process.contains_program(import) {
                bail!("Cannot add program '{}' because its import '{import}' must be added first", program.id())
            }
            // Retrieve the external stack for the import program ID.
            let external_stack = process.get_stack(import)?;
            // Add the external stack to the stack.
            stack.insert_external_stack(external_stack.clone())?;
        }
        // Add the program closures to the stack.
        for closure in program.closures().values() {
            // Add the closure to the stack.
            stack.insert_closure(closure)?;
        }
        // Add the program functions to the stack.
        for function in program.functions().values() {
            // Add the function to the stack.
            stack.insert_function(function)?;
        }
        // Return the stack.
        Ok(stack)
    }
}

impl<N: Network> Stack<N> {
    /// Inserts the given external stack to the stack.
    #[inline]
    fn insert_external_stack(&mut self, external_stack: Stack<N>) -> Result<()> {
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

    /// Inserts the given closure to the stack.
    #[inline]
    fn insert_closure(&mut self, closure: &Closure<N>) -> Result<()> {
        // Retrieve the closure name.
        let name = closure.name();
        // Ensure the closure name is not already added.
        ensure!(!self.register_types.contains_key(name), "Closure '{name}' already exists");

        // Compute the register types.
        let register_types = RegisterTypes::from_closure(self, closure)?;
        // Add the closure name and register types to the stack.
        self.register_types.insert(*name, register_types);
        // Return success.
        Ok(())
    }

    /// Adds the given function name and register types to the stack.
    #[inline]
    fn insert_function(&mut self, function: &Function<N>) -> Result<()> {
        // Retrieve the function name.
        let name = function.name();
        // Ensure the function name is not already added.
        ensure!(!self.register_types.contains_key(name), "Function '{name}' already exists");

        // Compute the register types.
        let register_types = RegisterTypes::from_function(self, function)?;
        // Add the function name and register types to the stack.
        self.register_types.insert(*name, register_types);

        // If the function contains a finalize, insert it.
        if let Some((_, finalize)) = function.finalize() {
            // Compute the finalize types.
            let finalize_types = FinalizeTypes::from_finalize(self, finalize)?;
            // Add the finalize name and finalize types to the stack.
            self.finalize_types.insert(*name, finalize_types);
        }

        // Return success.
        Ok(())
    }
}
