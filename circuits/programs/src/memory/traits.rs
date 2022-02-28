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

use crate::{Immediate, Instruction, Register};
use snarkvm_circuits::Environment;

use core::hash;

pub trait Memory: Copy + Clone + Eq + PartialEq + hash::Hash {
    type Environment: Environment;

    /// Allocates a new register in memory, returning the new register.
    fn new_register() -> Register<Self::Environment>;

    /// Returns `true` if the given register is already set.
    fn is_set(register: &Register<Self::Environment>) -> bool;

    /// Attempts to load the value from the register.
    fn load(register: &Register<Self::Environment>) -> Immediate<Self::Environment>;

    /// Attempts to store value into the register.
    fn store(register: &Register<Self::Environment>, value: Immediate<Self::Environment>);

    /// Returns the number of registers allocated.
    fn num_registers() -> u64;

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        Self::Environment::halt(message)
    }

    /// Clears and initializes an empty memory layout.
    fn reset();
}
