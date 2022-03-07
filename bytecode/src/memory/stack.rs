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

use crate::{Immediate, Memory, Register};
use snarkvm_circuits::Environment;

use core::cell::RefCell;
use once_cell::unsync::OnceCell;
use std::{collections::HashMap, rc::Rc};

#[derive(Clone)]
pub struct Stack<E: Environment> {
    registers: Rc<RefCell<HashMap<Register<E>, OnceCell<Immediate<E>>>>>,
}

impl<E: Environment> Memory for Stack<E> {
    type Environment = E;

    /// Allocates the given register in memory. Ensures the given register does not exist already.
    fn initialize(&self, register: &Register<E>) {
        // TODO (howardwu): Handle this assert as a haltable event.
        assert_eq!(**register, self.registers.borrow().len() as u64);

        // Ensure the register has not be initialized, and initialize it.
        match !self.exists(register) {
            true => self.registers.borrow_mut().insert(*register, Default::default()),
            false => Self::halt(format!("Tried to re-initialize existing register {}", register)),
        };
    }

    /// Returns `true` if the given register exists.
    fn exists(&self, register: &Register<E>) -> bool {
        self.registers.borrow().contains_key(register)
    }

    /// Returns `true` if the given register both exists and is set.
    fn is_set(&self, register: &Register<E>) -> bool {
        // Attempt to retrieve the specified register from memory.
        match self.registers.borrow().get(register) {
            // Check if the register is set.
            Some(memory) => memory.get().is_some(),
            None => false,
        }
    }

    /// Attempts to load the immediate from the register.
    fn load(&self, register: &Register<E>) -> Immediate<E> {
        // Attempt to retrieve the specified register from memory.
        match self.registers.borrow().get(register) {
            // Attempt to retrieve the value the specified register.
            Some(memory) => match memory.get() {
                Some(immediate) => immediate.clone(),
                None => Self::halt(format!("Register {} is not set", register)),
            },
            None => Self::halt(format!("Register {} does not exist", register)),
        }
    }

    /// Attempts to store immediate into the register.
    fn store(&self, register: &Register<E>, immediate: Immediate<E>) {
        // Attempt to retrieve the specified register from memory.
        match self.registers.borrow().get(register) {
            // Attempt to set the specified register with the given value.
            Some(memory) => {
                if memory.set(immediate).is_err() {
                    Self::halt(format!("Register {} is already set", register))
                }
            }
            None => Self::halt(format!("Register {} does not exist", register)),
        }
    }

    /// Returns the number of registers allocated.
    fn num_registers(&self) -> u64 {
        self.registers.borrow().len() as u64
    }
}

impl<E: Environment> Default for Stack<E> {
    fn default() -> Self {
        Self { registers: Default::default() }
    }
}
