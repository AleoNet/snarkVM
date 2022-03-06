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

use crate::{Argument, Immediate, Register};
use snarkvm_circuits::Environment;

use once_cell::unsync::OnceCell;
use std::collections::HashMap;

pub(super) struct Allocator<E: Environment> {
    inputs: HashMap<u64, Immediate<E>>,
    registers: HashMap<Register<E>, OnceCell<Immediate<E>>>,
    outputs: Vec<Register<E>>,
}

impl<E: Environment> Allocator<E> {
    /// Allocates a new input in memory, returning the new register.
    pub(super) fn new_input(&mut self, input: Immediate<E>) -> Register<E> {
        let register = Register::new(self.inputs.len() as u64);
        self.inputs.insert(*register, input);
        self.registers.insert(register, Default::default());
        register
    }

    /// Attempts to retrieve the input value from the given argument.
    pub(super) fn load_input(&self, argument: &Argument<E>) -> Immediate<E> {
        // Attempt to retrieve the specified register from memory.
        let immediate = match self.inputs.get(&**argument.register()) {
            Some(immediate) => immediate,
            None => E::halt(format!("Input register {} does not exist", argument.register())),
        };

        // Ensure the type and mode are correct.
        match immediate.type_name() == argument.type_name() && &immediate.mode() == argument.mode() {
            true => immediate.clone(),
            false => E::halt(format!(
                "Input register {} is not a {} {}",
                argument.register(),
                argument.mode(),
                argument.type_name()
            )),
        }
    }

    /// Returns the number of input registers allocated.
    pub(super) fn num_inputs(&self) -> u64 {
        self.inputs.len() as u64
    }
}

impl<E: Environment> Allocator<E> {
    /// Allocates a new register in memory, returning the new register.
    pub(super) fn new_register(&mut self) -> Register<E> {
        let register = Register::new(self.registers.len() as u64);
        self.registers.insert(register, Default::default());
        register
    }

    /// Allocates the given register in memory.
    pub(super) fn initialize(&mut self, register: &Register<E>) {
        if !self.exists(register) {
            self.registers.insert(*register, Default::default());
        }
    }

    /// Returns `true` if the given register exists.
    pub(super) fn exists(&self, register: &Register<E>) -> bool {
        self.registers.contains_key(register)
    }

    /// Returns `true` if the given register is already set.
    pub(super) fn is_set(&self, register: &Register<E>) -> bool {
        // Attempt to retrieve the specified register from memory.
        match self.registers.get(register) {
            // Check if the register is set.
            Some(memory) => memory.get().is_some(),
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
        match memory.get() {
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
        if memory.set(value).is_err() {
            E::halt(format!("Register {} is already set", register))
        }
    }

    /// Returns the number of registers allocated.
    pub(super) fn num_registers(&self) -> u64 {
        self.registers.len() as u64
    }
}

impl<E: Environment> Allocator<E> {
    /// Attempts to store the register of the given argument as an output.
    pub(super) fn store_output(&mut self, argument: &Argument<E>) {
        let register = argument.register();
        self.outputs.push(*register);

        // Attempt to retrieve the specified register from memory.
        let memory = match self.registers.get(register) {
            Some(memory) => memory,
            None => E::halt(format!("Output register {} does not exist", register)),
        };

        // Attempt to retrieve the value the specified register.
        let immediate = match memory.get() {
            Some(immediate) => immediate,
            None => E::halt(format!("Output register {} is missing", register)),
        };

        // Ensure the type and mode are correct.
        match immediate.type_name() == argument.type_name() && &immediate.mode() == argument.mode() {
            true => (),
            false => E::halt(format!(
                "Output register {} is not a {} {}",
                argument.register(),
                argument.mode(),
                argument.type_name()
            )),
        }
    }

    /// Attempts to retrieve the output value from the given argument.
    pub(super) fn load_outputs(&self) -> Vec<Immediate<E>> {
        let mut outputs = Vec::with_capacity(self.outputs.len());
        for register in &self.outputs {
            outputs.push(self.load(&register));
        }
        outputs
    }

    /// Returns the number of output registers allocated.
    pub(super) fn num_outputs(&self) -> u64 {
        self.outputs.len() as u64
    }
}

impl<E: Environment> Default for Allocator<E> {
    fn default() -> Self {
        Self { inputs: Default::default(), registers: Default::default(), outputs: Default::default() }
    }
}
