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

use snarkvm_circuits::{traits::*, Affine, BaseField, Boolean, Circuit, Environment};
use snarkvm_circuits_programs::{Function, Immediate, Instruction, Operand, Registers};

use once_cell::unsync::OnceCell;
use std::{cell::RefCell, rc::Rc};

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

fn main() {
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
