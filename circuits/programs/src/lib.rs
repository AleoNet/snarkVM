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

use snarkvm_circuits::{traits::*, Affine, BaseField, Boolean, Environment};

use once_cell::unsync::OnceCell;
use std::{cell::RefCell, rc::Rc};

#[derive(Clone)]
pub enum Immediate<E: Environment> {
    Boolean(Boolean<E>),
    BaseField(BaseField<E>),
    Group(Affine<E>),
}

#[derive(Clone)]
pub enum Operand<E: Environment> {
    Immediate(Immediate<E>),
    Register(Register<E>),
}

impl<E: Environment> Operand<E> {
    /// Returns `true` if the value type is a register.
    fn is_register(&self) -> bool {
        matches!(self, Self::Register(..))
    }

    /// Returns the value from a register, otherwise passes the loaded value through.
    fn to_value(&self) -> Immediate<E> {
        match self {
            Self::Immediate(value) => value.clone(),
            Self::Register(register) => register.load(),
        }
    }
}

impl<E: Environment> From<Immediate<E>> for Operand<E> {
    fn from(immediate: Immediate<E>) -> Operand<E> {
        Operand::Immediate(immediate)
    }
}

impl<E: Environment> From<&Immediate<E>> for Operand<E> {
    fn from(immediate: &Immediate<E>) -> Operand<E> {
        Operand::from(immediate.clone())
    }
}

impl<E: Environment> From<Register<E>> for Operand<E> {
    fn from(register: Register<E>) -> Operand<E> {
        Operand::Register(register)
    }
}

impl<E: Environment> From<&Register<E>> for Operand<E> {
    fn from(register: &Register<E>) -> Operand<E> {
        Operand::from(register.clone())
    }
}

#[derive(Clone)]
pub struct Register<E: Environment>(u32, Rc<RefCell<OnceCell<Immediate<E>>>>);

impl<E: Environment> Register<E> {
    /// Returns a new instance of a register.
    fn new(locator: u32) -> Register<E> {
        Self(locator, Default::default())
    }

    /// Returns `true` if the register at the given locator is already set.
    fn is_set(&self) -> bool {
        self.1.borrow().get().is_some()
    }

    /// Attempts to store value into the register.
    fn store(&self, value: Immediate<E>) {
        match self.1.borrow().get().is_some() {
            true => panic!("Register {} is already set", self.0),
            false => {
                if self.1.borrow().set(value).is_err() {
                    panic!("Register {} failed to store value", self.0);
                }
            }
        }
    }

    /// Attempts to load the value from the register.
    fn load(&self) -> Immediate<E> {
        match self.1.borrow().get() {
            Some(value) => value.clone(),
            None => panic!("Register {} is not set", self.0),
        }
    }
}

pub type Registers<E> = Vec<Register<E>>;

pub enum Instruction<E: Environment> {
    /// Stores `operand` into `register`, if `register` is not already set.
    Store(Register<E>, Operand<E>),
    /// Adds `first` with `second`, storing the outcome in `register`.
    Add(Register<E>, Operand<E>, Operand<E>),
    /// Subtracts `first` from `second`, storing the outcome in `register`.
    Sub(Register<E>, Operand<E>, Operand<E>),
}

impl<E: Environment> Instruction<E> {
    /// Returns the opcode of the instruction.
    fn opcode(&self) -> u16 {
        match self {
            Self::Store(..) => 0,
            Self::Add(..) => 1,
            Self::Sub(..) => 2,
        }
    }

    /// Evaluates the instruction.
    fn evaluate(&self) {
        match self {
            Self::Store(register, operand) => Self::store(register, operand),
            Self::Add(register, first, second) => Self::add(register, first, second),
            Self::Sub(register, first, second) => Self::sub(register, first, second),
        }
    }

    /// Stores `operand` into `register`, if `register` is not already set.
    fn store(register: &Register<E>, operand: &Operand<E>) {
        register.store(operand.to_value())
    }

    /// Adds `first` with `second`, storing the outcome in `register`.
    fn add(register: &Register<E>, first: &Operand<E>, second: &Operand<E>) {
        match (first.to_value(), second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => register.store(Immediate::BaseField(a + b)),
            (Immediate::Group(a), Immediate::Group(b)) => register.store(Immediate::Group(a + b)),
            _ => E::halt("Invalid 'add' instruction"),
        }
    }

    /// Subtracts `first` from `second`, storing the outcome in `register`.
    fn sub(register: &Register<E>, first: &Operand<E>, second: &Operand<E>) {
        match (first.to_value(), second.to_value()) {
            (Immediate::BaseField(a), Immediate::BaseField(b)) => register.store(Immediate::BaseField(a - b)),
            (Immediate::Group(a), Immediate::Group(b)) => register.store(Immediate::Group(a - b)),
            _ => E::halt("Invalid 'sub' instruction"),
        }
    }
}

pub struct Function<E: Environment> {
    registers: Registers<E>,
    instructions: Vec<Instruction<E>>,
}

impl<E: Environment> Function<E> {
    /// Initializes a new instance of a function.
    fn new() -> Self {
        Self { registers: Registers::default(), instructions: Vec::new() }
    }

    /// Allocates a new register in memory, returning the new register.
    fn new_register(&mut self) -> Register<E> {
        let register = Register::new(self.registers.len() as u32);
        self.registers.push(register.clone());
        register
    }

    /// Allocates a new register, adds an instruction to store the given input, and returns the new register.
    fn new_input(&mut self, input: Operand<E>) -> Register<E> {
        let register = self.new_register();
        self.push_instruction(Instruction::Store(register.clone(), input));
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
        self.registers.len() as u32
    }
}

pub struct HelloWorld<E: Environment> {
    function: Function<E>,
    outputs: Registers<E>,
}

impl<E: Environment> HelloWorld<E> {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn new(inputs: [Operand<E>; 2]) -> Self {
        let mut function = Function::new();
        let mut outputs = Registers::new();

        // Allocate a new register for each input, and store each input in the register.
        let mut registers = Registers::with_capacity(2);
        for input in inputs {
            registers.push(function.new_input(input));
        }

        // Add the values in the registers, storing the result in a newly allocated register.
        for pair in registers.chunks(2) {
            let first = Operand::Register(pair[0].clone());
            let second = Operand::Register(pair[1].clone());
            let output = function.new_register();

            let instruction = Instruction::Add(output.clone(), first, second);

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
    use snarkvm_circuits::Circuit;

    #[test]
    fn test_hello_world() {
        let first = Immediate::BaseField(BaseField::<Circuit>::one());
        let second = Immediate::BaseField(BaseField::one());

        let function = HelloWorld::new([first.into(), second.into()]);
        function.run();

        let expected = BaseField::one() + BaseField::one();
        match function.outputs[0].load() {
            Immediate::BaseField(output) => assert!(output.is_eq(&expected).eject_value()),
            _ => panic!("Failed to load output"),
        }
    }
}

// pub struct Memory<E: Environment> {
//     registers: Registers<E>,
// }
//
// impl<E: Environment> Memory<E> {
//     /// Allocates a new register in memory, returning the new register.
//     fn new_register(&mut self) -> Register<E> {
//         let register = Register::new(self.registers.len() as u32);
//         self.registers.push(register.clone());
//         register
//     }
//
//     /// Returns the number of registers allocated.
//     fn num_registers(&self) -> u32 {
//         self.registers.len() as u32
//     }
// }
//
// impl<E: Environment> From<Registers<E>> for Memory<E> {
//     /// Returns an instance of memory from registers.
//     fn from(registers: Registers<E>) -> Self {
//         Self { registers }
//     }
// }
//
// impl<E: Environment> Default for Memory<E> {
//     /// Returns a new instance of memory.
//     fn default() -> Self {
//         Self::from(Registers::<E>::default())
//     }
// }
