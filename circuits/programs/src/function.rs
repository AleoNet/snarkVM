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

use crate::{Instruction, Operand, Register};
use snarkvm_circuits::Environment;

pub type Registers<E> = Vec<Register<E>>;

pub struct Function<E: Environment> {
    registers: Registers<E>,
    instructions: Vec<Instruction<E>>,
}

impl<E: Environment> Function<E> {
    /// Initializes a new instance of a function.
    pub fn new() -> Self {
        Self { registers: Registers::default(), instructions: Vec::new() }
    }

    /// Allocates a new register in memory, returning the new register.
    pub fn new_register(&mut self) -> Register<E> {
        let register = Register::new(self.registers.len() as u32);
        self.registers.push(register.clone());
        register
    }

    /// Allocates a new register, adds an instruction to store the given input, and returns the new register.
    pub fn new_input(&mut self, input: Operand<E>) -> Register<E> {
        let register = self.new_register();
        self.push_instruction(Instruction::Store(register.clone(), input));
        register
    }

    /// Adds the given instruction.
    pub fn push_instruction(&mut self, instruction: Instruction<E>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function.
    pub fn evaluate(&self) {
        for instruction in &self.instructions {
            instruction.evaluate();
        }
    }

    /// Returns the number of registers allocated.
    pub fn num_registers(&self) -> u32 {
        self.registers.len() as u32
    }
}

// pub struct Memory<E: Environment> {
//     registers: Registers<E>,
// }
//
// impl<E: Environment> Memory<E> {
//     /// Allocates a new register in memory, returning the new register.
//     fn new_register(&mut self) -> Register<E> {
//         let register = Register::new(self.registers.len() as u32);
//         self.registers.push(register.clone());
//         register
//     }
//
//     /// Returns the number of registers allocated.
//     fn num_registers(&self) -> u32 {
//         self.registers.len() as u32
//     }
// }
//
// impl<E: Environment> From<Registers<E>> for Memory<E> {
//     /// Returns an instance of memory from registers.
//     fn from(registers: Registers<E>) -> Self {
//         Self { registers }
//     }
// }
//
// impl<E: Environment> Default for Memory<E> {
//     /// Returns a new instance of memory.
//     fn default() -> Self {
//         Self::from(Registers::<E>::default())
//     }
// }
