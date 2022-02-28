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

use crate::{Immediate, Register};
use snarkvm_circuits::Environment;

use core::cell::RefCell;
use once_cell::unsync::OnceCell;
use std::{collections::HashMap, rc::Rc};

pub(super) struct Allocator<E: Environment> {
    registers: HashMap<Register<E>, Rc<RefCell<OnceCell<Immediate<E>>>>>,
}

impl<E: Environment> Allocator<E> {
    /// Allocates a new register in memory, returning the new register.
    pub(super) fn new_register(&mut self) -> Register<E> {
        let register = Register::new(self.registers.len() as u64);
        self.registers.insert(register, Default::default());
        register
    }

    /// Returns `true` if the given register is already set.
    pub(super) fn is_set(&self, register: &Register<E>) -> bool {
        // Attempt to retrieve the specified register from memory.
        match self.registers.get(register) {
            // Check if the register is set.
            Some(memory) => memory.borrow().get().is_some(),
            None => false,
        }
    }

    /// Attempts to load the value from the register.
    pub(super) fn load(&self, register: &Register<E>) -> Immediate<E> {
        // Attempt to retrieve the specified register from memory.
        let memory = match self.registers.get(register) {
            Some(memory) => memory,
            None => E::halt(format!("Register {} does not exist", register)),
        };

        // Attempt to retrieve the value the specified register.
        match memory.borrow().get() {
            Some(value) => value.clone(),
            None => E::halt(format!("Register {} is not set", register)),
        }
    }

    /// Attempts to store value into the register.
    pub(super) fn store(&self, register: &Register<E>, value: Immediate<E>) {
        // Attempt to retrieve the specified register from memory.
        let memory = match self.registers.get(register) {
            Some(memory) => memory,
            None => E::halt(format!("Register {} does not exist", register)),
        };

        // Attempt to set the specified register with the given value.
        match memory.borrow().get().is_some() {
            true => E::halt(format!("Register {} is already set", register)),
            false => {
                if memory.borrow().set(value).is_err() {
                    E::halt(format!("Register {} failed to store value", register))
                }
            }
        }
    }

    /// Returns the number of registers allocated.
    pub(super) fn num_registers(&self) -> u64 {
        self.registers.len() as u64
    }
}

impl<E: Environment> Default for Allocator<E> {
    fn default() -> Self {
        Self { registers: Default::default() }
    }
}
