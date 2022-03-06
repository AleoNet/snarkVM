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

use crate::{memory::allocator::Allocator, Argument, Immediate, Memory, Register};
use snarkvm_circuits::{Circuit, Environment};

use core::cell::RefCell;
use once_cell::unsync::Lazy;

thread_local! {
    static STACK: Lazy<RefCell<Allocator<Circuit>>> = Lazy::new(|| RefCell::new(Default::default()));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Stack;

impl Memory for Stack {
    type Environment = Circuit;

    /// Allocates the given register in memory. Ensures the given register does not exist already.
    fn initialize(register: &Register<Self::Environment>) {
        STACK.with(|stack| (**stack).borrow_mut().initialize(register))
    }

    /// Returns `true` if the given register exists.
    fn exists(register: &Register<Self::Environment>) -> bool {
        STACK.with(|stack| (**stack).borrow().exists(register))
    }

    /// Returns `true` if the given register both exists and is set.
    fn is_set(register: &Register<Self::Environment>) -> bool {
        STACK.with(|stack| (**stack).borrow().is_set(register))
    }

    /// Attempts to load the immediate from the register.
    fn load(register: &Register<Self::Environment>) -> Immediate<Self::Environment> {
        STACK.with(|stack| (**stack).borrow().load(register))
    }

    /// Attempts to store the immediate into the register.
    fn store(register: &Register<Self::Environment>, immediate: Immediate<Self::Environment>) {
        STACK.with(|stack| (**stack).borrow().store(register, immediate))
    }

    /// Returns the number of registers allocated.
    fn num_registers() -> u64 {
        STACK.with(|stack| (**stack).borrow().num_registers())
    }

    /// Clears and initializes an empty memory layout.
    fn reset() {
        Self::Environment::reset();
        STACK.with(|stack| *(**stack).borrow_mut() = Default::default());
    }
}
