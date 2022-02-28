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

use snarkvm_circuits::{traits::*, BaseField, Circuit};
use snarkvm_circuits_programs::{Function, Immediate, Instruction, Memory, Operand, Register, Registers};

pub struct HelloWorld<M: Memory> {
    function: Function<M>,
}

impl<M: Memory> HelloWorld<M> {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn new(inputs: [Immediate<M::Environment>; 2]) -> Self {
        let mut function = Function::new();

        // Allocate a new register for each input, and store each input in the register.
        let mut registers = Vec::with_capacity(2);
        for input in inputs {
            assert!(!input.is_constant());
            registers.push(function.new_input(input));
        }

        // Add the values in the registers, storing the result in a newly allocated register.
        for pair in registers.chunks(2) {
            let first = Operand::Register(pair[0].clone());
            let second = Operand::Register(pair[1].clone());
            let output = function.new_output();

            function.push_instruction(Instruction::Add(output, first, second));
        }

        Self { function }
    }

    pub fn run(&self) {
        self.function.evaluate();
    }

    pub fn outputs(&self) -> &Vec<Register<M::Environment>> {
        self.function.outputs()
    }
}

fn main() {
    let first = Immediate::BaseField(BaseField::<Circuit>::from_str("Public(1base)"));
    let second = Immediate::BaseField(BaseField::from_str("Private(1base)"));

    let function = HelloWorld::<Registers>::new([first, second]);
    function.run();

    let expected = BaseField::one() + BaseField::one();
    match Registers::load(&function.outputs()[0]) {
        Immediate::BaseField(output) => assert!(output.is_eq(&expected).eject_value()),
        _ => panic!("Failed to load output"),
    }
}

#[test]
fn test_hello_world() {
    let first = Immediate::BaseField(BaseField::<Circuit>::from_str("Public(1base)"));
    let second = Immediate::BaseField(BaseField::from_str("Private(1base)"));

    let function = HelloWorld::<Registers>::new([first, second]);
    function.run();

    let expected = BaseField::one() + BaseField::one();
    match Registers::load(&function.outputs()[0]) {
        Immediate::BaseField(output) => assert!(output.is_eq(&expected).eject_value()),
        _ => panic!("Failed to load output"),
    }
}
