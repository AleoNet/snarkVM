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

use crate::{instructions::Instruction, Immediate, Memory, Register};

pub(super) struct Local<M: Memory> {
    inputs: Vec<Register<M::Environment>>,
    instructions: Vec<Instruction<M>>,
    outputs: Vec<Register<M::Environment>>,
}

impl<M: Memory> Local<M> {
    /// Allocates a new register, stores the given input, and returns the new register.
    pub fn new_input(&mut self, input: Immediate<M::Environment>) -> Register<M::Environment> {
        match input.is_constant() {
            true => M::halt("Attempted to assign a constant value as an input"),
            false => {
                let register = M::new_register();
                self.inputs.push(register);
                M::store(&register, input);
                register
            }
        }
    }

    /// Allocates a new register, stores the given output, and returns the new register.
    pub fn new_output(&mut self) -> Register<M::Environment> {
        let register = M::new_register();
        self.outputs.push(register);
        register
    }

    /// Adds the given instruction.
    pub fn push_instruction(&mut self, instruction: Instruction<M>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function, returning the outputs.
    pub fn evaluate(&self) -> Vec<Immediate<M::Environment>> {
        for instruction in &self.instructions {
            instruction.evaluate();
        }

        let mut outputs = Vec::with_capacity(self.outputs.len());
        for output in &self.outputs {
            outputs.push(M::load(output));
        }
        outputs
    }
}

impl<M: Memory> Default for Local<M> {
    fn default() -> Self {
        Self { inputs: Default::default(), instructions: Default::default(), outputs: Default::default() }
    }
}
