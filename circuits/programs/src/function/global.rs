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

use crate::{function::local::Local, Function, Immediate, Instruction, Memory, Register, Stack};

use core::cell::RefCell;
use once_cell::unsync::Lazy;

thread_local! {
    static FUNCTION: Lazy<RefCell<Local<Stack>>> = Lazy::new(|| RefCell::new(Default::default()));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Global;

impl Function for Global {
    type Environment = <Self::Memory as Memory>::Environment;
    type Memory = Stack;

    /// Allocates a new register, stores the given input, and returns the new register.
    fn new_input(input: Immediate<Self::Environment>) -> Register<Self::Environment> {
        FUNCTION.with(|function| (**function).borrow_mut().new_input(input))
    }

    /// Allocates a new register, stores the given output, and returns the new register.
    fn new_output() -> Register<Self::Environment> {
        FUNCTION.with(|function| (**function).borrow_mut().new_output())
    }

    /// Adds the given instruction.
    fn push_instruction(instruction: Instruction<Self::Memory>) {
        FUNCTION.with(|function| (**function).borrow_mut().push_instruction(instruction))
    }

    /// Evaluates the function, returning the outputs.
    fn evaluate() -> Vec<Immediate<Self::Environment>> {
        FUNCTION.with(|function| (**function).borrow().evaluate())
    }
}
