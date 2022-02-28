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
use snarkvm_circuits::Environment;

use core::hash;

pub trait Function: Copy + Clone + Eq + PartialEq + hash::Hash {
    type Environment: Environment;
    type Memory: Memory<Environment = Self::Environment>;

    /// Allocates a new register, stores the given input, and returns the new register.
    fn new_input(input: Immediate<Self::Environment>) -> Register<Self::Environment>;

    /// Allocates a new register, stores the given output, and returns the new register.
    fn new_output() -> Register<Self::Environment>;

    /// Adds the given instruction.
    fn push_instruction(instruction: Instruction<Self::Memory>);

    /// Evaluates the function, returning the outputs.
    fn evaluate() -> Vec<Immediate<Self::Environment>>;
}
