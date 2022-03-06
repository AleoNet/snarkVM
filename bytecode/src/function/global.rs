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

use crate::{
    function::local::Local,
    instructions::Instruction,
    CoreMemory,
    Function,
    Immediate,
    Memory,
    Register,
    Stack,
};
use snarkvm_circuits::{Parser, ParserResult};

use core::{cell::RefCell, fmt};
use once_cell::unsync::Lazy;

thread_local! {
    static FUNCTION: Lazy<RefCell<Local<Stack>>> = Lazy::new(|| RefCell::new(Default::default()));
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Global;

impl Function for Global {
    type Environment = <Self::Memory as CoreMemory>::Environment;
    type Memory = Stack;

    /// Allocates a new register, stores the given input, and returns the new register.
    fn new_input(input: Immediate<<Self as Function>::Environment>) -> Register<<Self as Function>::Environment> {
        FUNCTION.with(|function| (**function).borrow_mut().new_input(input))
    }

    /// Adds the given instruction.
    fn push_instruction(instruction: Instruction<Self::Memory>) {
        FUNCTION.with(|function| (**function).borrow_mut().push_instruction(instruction))
    }

    /// Evaluates the function, returning the outputs.
    fn evaluate() -> Vec<Immediate<<Self as Function>::Environment>> {
        FUNCTION.with(|function| (**function).borrow().evaluate())
    }

    /// Clears and initializes a new function layout.
    fn reset() {
        Self::Memory::reset();
        FUNCTION.with(|function| *(**function).borrow_mut() = Default::default());
    }
}

impl Parser for Global {
    type Environment = <<Self as Function>::Memory as CoreMemory>::Environment;

    /// Parses a string into a global function.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        match Local::parse(string) {
            Ok((string, local)) => {
                // <Self as Function>::Memory::reset();
                FUNCTION.with(|function| *(**function).borrow_mut() = local);
                Ok((string, Self))
            }
            Err(error) => Err(error),
        }
    }
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        FUNCTION.with(|function| (**function).borrow().fmt(f))
    }
}
