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

use crate::{Immediate, Instruction, Memory, Register};

pub struct Function<M: Memory> {
    inputs: Vec<Instruction<M>>,
    instructions: Vec<Instruction<M>>,
    outputs: Vec<Register<M::Environment>>,
}

impl<M: Memory> Function<M> {
    /// Initializes a new instance of a function.
    pub fn new() -> Self {
        Self { inputs: Vec::new(), instructions: Vec::new(), outputs: Vec::new() }
    }

    /// Allocates a new register, adds an instruction to store the given input, and returns the new register.
    pub fn new_input(&mut self, input: Immediate<M::Environment>) -> Register<M::Environment> {
        let register = M::new_register();
        self.inputs.push(Instruction::Store(register, input.into()));
        register
    }

    /// Allocates a new register, adds an instruction to store the given output, and returns the new register.
    pub fn new_output(&mut self) -> Register<M::Environment> {
        let register = M::new_register();
        self.outputs.push(register);
        register
    }

    /// Adds the given instruction.
    pub fn push_instruction(&mut self, instruction: Instruction<M>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function.
    pub fn evaluate(&self) {
        for instruction in &self.inputs {
            instruction.evaluate();
        }
        for instruction in &self.instructions {
            instruction.evaluate();
        }
    }

    /// Returns the output registers.
    pub fn outputs(&self) -> &Vec<Register<M::Environment>> {
        &self.outputs
    }
}
