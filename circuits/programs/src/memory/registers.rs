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

use crate::{memory::registry::Registry, Immediate, Memory, Register};
use snarkvm_circuits::Circuit;

use core::cell::RefCell;
use once_cell::unsync::Lazy;

thread_local! {
    static REGISTERS: Lazy<RefCell<Registry<Circuit>>> = Lazy::new(|| RefCell::new(Default::default()));
}

pub struct Registers;

impl Memory for Registers {
    type Environment = Circuit;

    /// Allocates a new register in memory, returning the new register.
    fn new_register() -> Register {
        REGISTERS.with(|registers| (**registers).borrow_mut().new_register())
    }

    /// Returns `true` if the given register is already set.
    fn is_set(register: &Register) -> bool {
        REGISTERS.with(|registers| (**registers).borrow().is_set(register))
    }

    /// Attempts to store value into the register.
    fn store(register: &Register, value: Immediate<Self::Environment>) {
        REGISTERS.with(|registers| (**registers).borrow().store(register, value))
    }

    /// Attempts to load the value from the register.
    fn load(register: &Register) -> Immediate<Self::Environment> {
        REGISTERS.with(|registers| (**registers).borrow().load(register))
    }

    /// Returns the number of registers allocated.
    fn num_registers() -> u64 {
        REGISTERS.with(|registers| (**registers).borrow().num_registers())
    }

    /// Clears and initializes an empty memory layout.
    fn reset() {
        REGISTERS.with(|registers| *(**registers).borrow_mut() = Default::default());
    }
}
