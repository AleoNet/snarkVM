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

use crate::{memory::allocator::Allocator, Immediate, Instruction, Memory, Register};
use snarkvm_circuits::Circuit;

use core::cell::RefCell;
use once_cell::unsync::Lazy;

thread_local! {
    static STACK: Lazy<RefCell<Allocator<Circuit>>> = Lazy::new(|| RefCell::new(Default::default()));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Stack;

impl Memory for Stack {
    type Environment = Circuit;

    /// Allocates a new register in memory, returning the new register.
    fn new_register() -> Register<Self::Environment> {
        STACK.with(|stack| (**stack).borrow_mut().new_register())
    }

    /// Returns `true` if the given register is already set.
    fn is_set(register: &Register<Self::Environment>) -> bool {
        STACK.with(|stack| (**stack).borrow().is_set(register))
    }

    /// Attempts to load the value from the register.
    fn load(register: &Register<Self::Environment>) -> Immediate<Self::Environment> {
        STACK.with(|stack| (**stack).borrow().load(register))
    }

    /// Attempts to store value into the register.
    fn store(register: &Register<Self::Environment>, value: Immediate<Self::Environment>) {
        STACK.with(|stack| (**stack).borrow().store(register, value))
    }

    /// Returns the number of registers allocated.
    fn num_registers() -> u64 {
        STACK.with(|stack| (**stack).borrow().num_registers())
    }

    /// Clears and initializes an empty memory layout.
    fn reset() {
        STACK.with(|stack| *(**stack).borrow_mut() = Default::default());
    }
}
