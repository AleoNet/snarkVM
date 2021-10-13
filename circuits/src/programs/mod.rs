// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{traits::*, Affine, Boolean, Environment, Field};

use itertools::Itertools;
use once_cell::unsync::OnceCell;
use std::{cell::RefCell, rc::Rc};

#[derive(Clone)]
pub enum Value<E: Environment> {
    Boolean(Boolean<E>),
    Field(Field<E>),
    Group(Affine<E>),
    Register(Register<E>),
}

impl<E: Environment> Value<E> {
    /// Returns `true` if the value type is a register.
    fn is_register(&self) -> bool {
        match self {
            Self::Register(..) => true,
            _ => false,
        }
    }

    /// Returns the value from a register, otherwise passes the loaded value through.
    fn to_value(&self) -> Value<E> {
        match self {
            Self::Register(register) => register.load(),
            value => value.clone(),
        }
    }
}

#[derive(Copy, Clone)]
struct Locator(u32);

#[derive(Clone)]
pub struct Register<E: Environment>(Locator, Rc<RefCell<Memory<E>>>);

impl<E: Environment> Register<E> {
    /// Returns `true` if the register at the given locator is already set.
    fn is_set(&self) -> bool {
        self.1.borrow().is_register_set(self.0)
    }

    /// Attempts to store value into the register.
    fn store(&self, value: &Value<E>) {
        self.1.borrow_mut().store(self.0, value);
    }

    /// Attempts to load the value from the register.
    fn load(&self) -> Value<E> {
        self.1.borrow().load(self.0).clone()
    }
}

pub struct Memory<E: Environment> {
    registers: Vec<OnceCell<Value<E>>>,
}

impl<E: Environment> Memory<E> {
    /// Initializes a new instance of memory.
    fn new() -> Self {
        Self {
            registers: Default::default(),
        }
    }

    /// Allocates a new register in memory, returning the new register locator.
    fn new_register(&mut self) -> Locator {
        let locator = Locator(self.registers.len() as u32);
        self.registers.push(OnceCell::new());
        locator
    }

    /// Returns `true` if the register at the given locator is already set.
    fn is_register_set(&self, locator: Locator) -> bool {
        match self.registers.get(locator.0 as usize) {
            Some(register) => register.get().is_some(),
            None => panic!("Failed to locate register {}", locator.0),
        }
    }

    /// Attempts to store value into the register.
    fn store(&self, locator: Locator, value: &Value<E>) {
        match self.registers.get(locator.0 as usize) {
            Some(register) => match register.get().is_some() {
                true => panic!("Register {} is already set", locator.0),
                false => register.set(value.clone()),
            },
            None => panic!("Failed to locate register {}", locator.0),
        };
    }

    /// Attempts to load the value from the register.
    fn load(&self, locator: Locator) -> &Value<E> {
        match self.registers.get(locator.0 as usize) {
            Some(register) => match register.get() {
                Some(value) => value,
                None => panic!("Register {} is not set", locator.0),
            },
            None => panic!("Failed to locate register {}", locator.0),
        }
    }

    /// Returns the number of registers allocated.
    fn num_registers(&self) -> u32 {
        self.registers.len() as u32
    }
}

pub enum Instruction<E: Environment> {
    /// Stores `value` into `register`, if `register` is not already set.
    Store(Value<E>, Register<E>),
    /// Adds `first` with `second`, storing the outcome in `register`.
    Add(Value<E>, Value<E>, Register<E>),
}

impl<E: Environment> Instruction<E> {
    /// Returns the opcode of the instruction.
    fn opcode(&self) -> u16 {
        match self {
            Self::Store(..) => 0,
            Self::Add(..) => 1,
        }
    }

    /// Evaluates the instruction.
    fn evaluate(&self) {
        match self {
            Self::Store(..) => self.store(),
            Self::Add(..) => self.add(),
        }
    }

    /// Stores `value` into `register`, if `register` is not already set.
    fn store(&self) {
        match self {
            Self::Store(value, register) => register.store(value),
            _ => unreachable!(),
        };
    }

    /// Adds `first` with `second`, storing the outcome in `register`.
    fn add(&self) {
        // Load the values and register.
        let (first, second, register) = match self {
            Self::Add(first, second, register) => (first, second, register),
            _ => unreachable!(),
        };

        // Perform the operation.
        match (first.to_value(), second.to_value()) {
            (Value::Field(a), Value::Field(b)) => register.store(&Value::Field(a + b)),
            (Value::Group(a), Value::Group(b)) => register.store(&Value::Group(a + b)),
            _ => unreachable!(),
        }
    }
}

pub struct Function<E: Environment> {
    memory: Rc<RefCell<Memory<E>>>,
    instructions: Vec<Instruction<E>>,
}

impl<E: Environment> Function<E> {
    /// Initializes a new instance of a function.
    fn new() -> Self {
        Self {
            memory: Rc::new(RefCell::new(Memory::new())),
            instructions: Vec::new(),
        }
    }

    /// Allocates a new register in memory, returning the new register.
    fn new_register(&mut self) -> Register<E> {
        let locator = self.memory.borrow_mut().new_register();
        Register(locator, self.memory.clone())
    }

    /// Allocates a new register, adds an instruction to store the given input, and returns the new register.
    fn new_input(&mut self, input: Value<E>) -> Register<E> {
        let register = self.new_register();
        self.push_instruction(Instruction::Store(input, register.clone()));
        register
    }

    /// Adds the given instruction.
    fn push_instruction(&mut self, instruction: Instruction<E>) {
        self.instructions.push(instruction);
    }

    /// Evaluates the function.
    fn evaluate(&self) {
        for instruction in &self.instructions {
            instruction.evaluate();
        }
    }

    /// Returns the number of registers allocated.
    fn num_registers(&self) -> u32 {
        self.memory.borrow().num_registers()
    }
}

pub struct HelloWorld<E: Environment> {
    function: Function<E>,
    outputs: Vec<Register<E>>,
}

impl<E: Environment> HelloWorld<E> {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn new(inputs: [Value<E>; 2]) -> Self {
        let mut function = Function::new();
        let mut outputs = Vec::new();

        // Allocate a new register for each input, and store each input in the register.
        let mut registers = Vec::with_capacity(2);
        for input in inputs {
            registers.push(function.new_input(input));
        }

        // Add the values in the registers, storing the result in a newly allocated register.
        for pair in registers.chunks(2) {
            let first = Value::Register(pair[0].clone());
            let second = Value::Register(pair[1].clone());
            let output = function.new_register();

            let instruction = Instruction::Add(first, second, output.clone());

            function.push_instruction(instruction);
            outputs.push(output);
        }

        Self { function, outputs }
    }

    pub fn run(&self) {
        self.function.evaluate();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_hello_world() {
        let first = Value::Field(Field::<Circuit>::one());
        let second = Value::Field(Field::one());

        let function = HelloWorld::new([first, second]);
        function.run();

        let expected = Field::one() + Field::one();
        match function.outputs[0].load() {
            Value::Field(output) => assert!(output.is_eq(&expected).eject_value()),
            _ => panic!("Failed to load output"),
        }
    }
}
