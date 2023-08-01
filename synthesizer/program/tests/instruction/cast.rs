// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::helpers::sample::{sample_finalize_registers, sample_registers};

use circuit::{AleoV0, Eject, Environment};
use console::{
    network::Testnet3,
    prelude::*,
    program::{Identifier, Literal, LiteralType, Plaintext, PlaintextType, Register, RegisterType, Value},
};
use snarkvm_synthesizer_program::{
    Cast,
    CastInstruction,
    CastLossy,
    CastType,
    Opcode,
    Operand,
    Program,
    RegistersLoad,
    RegistersLoadCircuit,
};
use synthesizer_process::{Process, Stack};

use std::panic::AssertUnwindSafe;

type CurrentNetwork = Testnet3;
type CurrentAleo = AleoV0;

const ITERATIONS: usize = 100;

/// Samples the stack. Note: Do not replicate this for real program use, it is insecure.
#[allow(clippy::type_complexity)]
fn sample_stack(
    opcode: Opcode,
    input_type: LiteralType,
    input_mode: circuit::Mode,
    output_type: LiteralType,
) -> Result<(Stack<CurrentNetwork>, Vec<Operand<CurrentNetwork>>, Register<CurrentNetwork>)> {
    // Initialize the opcode.
    let opcode = opcode.to_string();

    // Initialize the registers.
    let r0 = Register::Locator(0);
    let r1 = Register::Locator(1);

    // Initialize the program.
    let program = Program::from_str(&format!(
        "program testing.aleo;
            function test:
                input {r0} as {input_type}.{input_mode};
                {opcode} {r0} into {r1} as {output_type};
                finalize {r0};
            finalize test:
                input {r0} as {input_type}.public;
                {opcode} {r0} into {r1} as {output_type};
        "
    ))?;

    // Initialize the operands.
    let operands = vec![Operand::Register(r0)];

    // Initialize the stack.
    let stack = Stack::new(&Process::load()?, &program)?;

    Ok((stack, operands, r1))
}

fn check_cast<const VARIANT: u8>(
    operation: impl FnOnce(
        Vec<Operand<CurrentNetwork>>,
        Register<CurrentNetwork>,
        LiteralType,
    ) -> CastInstruction<CurrentNetwork, VARIANT>,
    opcode: Opcode,
    literal: &Literal<CurrentNetwork>,
    mode: &circuit::Mode,
    output_type: LiteralType,
) {
    // Initialize the types.
    let type_ = literal.to_type();

    // Initialize the stack.
    let (stack, operands, destination) = sample_stack(opcode, type_, *mode, output_type).unwrap();

    // Initialize the operation.
    let operation = operation(operands, destination.clone(), output_type);

    // Initialize the function name.
    let function_name = Identifier::from_str("test").unwrap();

    // Initialize a destination operand.
    let destination_operand = Operand::Register(destination);

    // Attempt to evaluate the valid operand case.
    let mut evaluate_registers = sample_registers(&stack, &function_name, &[(literal, None)]).unwrap();
    let result_a =
        std::panic::catch_unwind(AssertUnwindSafe(|| operation.evaluate(&stack, &mut evaluate_registers).unwrap()));

    // Attempt to execute the valid operand case.
    let mut execute_registers = sample_registers(&stack, &function_name, &[(literal, Some(*mode))]).unwrap();
    let result_b = std::panic::catch_unwind(AssertUnwindSafe(|| {
        operation.execute::<CurrentAleo>(&stack, &mut execute_registers).unwrap();
        assert!(CurrentAleo::is_satisfied())
    }));

    // Attempt to finalize the valid operand case.
    let mut finalize_registers = sample_finalize_registers(&stack, &function_name, &[literal]).unwrap();
    let result_c =
        std::panic::catch_unwind(AssertUnwindSafe(|| operation.finalize(&stack, &mut finalize_registers).unwrap()));

    // Check that either all operations failed, or all operations succeeded.
    println!("result_a: {:?}", result_a);
    println!("result_b: {:?}", result_b);
    println!("result_c: {:?}", result_c);
    let all_failed = result_a.is_err() && result_b.is_err() && result_c.is_err();
    let all_succeeded = result_a.is_ok() && result_b.is_ok() && result_c.is_ok();
    assert!(
        all_failed || all_succeeded,
        "The results of the evaluation, execution, and finalization should either all succeed or all fail"
    );

    // If all operations succeeded, check that the outputs are consistent.
    if all_succeeded {
        // Retrieve the output of evaluation.
        let output_a = evaluate_registers.load(&stack, &destination_operand).unwrap();

        // Retrieve the output of execution.
        let output_b = execute_registers.load_circuit(&stack, &destination_operand).unwrap();

        // Retrieve the output of finalization.
        let output_c = finalize_registers.load(&stack, &destination_operand).unwrap();

        // Check that the outputs are consistent.
        assert_eq!(output_a, output_b.eject_value(), "The results of the evaluation and execution are inconsistent");
        assert_eq!(output_a, output_c, "The results of the evaluation and finalization are inconsistent");

        // Check that the output type is consistent with the declared type.
        match output_a {
            Value::Plaintext(Plaintext::Literal(literal, _)) => {
                assert_eq!(literal.to_type(), output_type, "The output type is inconsistent with the declared type");
            }
            _ => unreachable!("The output type is inconsistent with the declared type"),
        }
    }
    // Reset the circuit.
    <CurrentAleo as circuit::Environment>::reset();
}

macro_rules! test_cast {
        ($input_type:ident, $output_type:ident) => {
            paste::paste! {
                #[test]
                fn [<test _ cast _ from _ $input_type:lower _ to _ $output_type:lower _ is _ consistent>]() {
                    // Initialize the operations.
                    let cast_operation = |operands, destination, output_type| Cast::<CurrentNetwork>::new(operands, destination, CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(output_type)))).unwrap();
                    let cast_lossy_operation = |operands, destination, output_type| CastLossy::<CurrentNetwork>::new(operands, destination, CastType::RegisterType(RegisterType::Plaintext(PlaintextType::Literal(output_type)))).unwrap();
                    // Initialize the opcodes.
                    let cast_opcode = Cast::<CurrentNetwork>::opcode();
                    let cast_lossy_opcode = CastLossy::<CurrentNetwork>::opcode();

                    // Prepare the rng.
                    let mut rng = TestRng::default();

                    // Prepare the test.
                    let modes = [circuit::Mode::Public, circuit::Mode::Private];

                    for _ in 0..ITERATIONS {
                        let literal = console::program::Literal::$input_type(Uniform::rand(&mut rng));
                        for mode in modes.iter() {
                            check_cast(cast_operation, cast_opcode, &literal, mode, LiteralType::$output_type);
                            check_cast(cast_lossy_operation, cast_lossy_opcode, &literal, mode, LiteralType::$output_type);
                        }
                    }
                }
            }
        };
    }

macro_rules! test_cast_for_all_literal_types {
    ($input_type:ident) => {
        test_cast!($input_type, Address);
        test_cast!($input_type, Boolean);
        test_cast!($input_type, Field);
        test_cast!($input_type, Group);
        test_cast!($input_type, I8);
        test_cast!($input_type, I16);
        test_cast!($input_type, I32);
        test_cast!($input_type, I64);
        test_cast!($input_type, I128);
        test_cast!($input_type, U8);
        test_cast!($input_type, U16);
        test_cast!($input_type, U32);
        test_cast!($input_type, U64);
        test_cast!($input_type, U128);
        test_cast!($input_type, Scalar);
    };
}

test_cast_for_all_literal_types!(Boolean);
test_cast_for_all_literal_types!(Field);
test_cast_for_all_literal_types!(Group);
test_cast_for_all_literal_types!(I8);
test_cast_for_all_literal_types!(I16);
test_cast_for_all_literal_types!(I32);
test_cast_for_all_literal_types!(I64);
test_cast_for_all_literal_types!(I128);
test_cast_for_all_literal_types!(U8);
test_cast_for_all_literal_types!(U16);
test_cast_for_all_literal_types!(U32);
test_cast_for_all_literal_types!(U64);
test_cast_for_all_literal_types!(U128);
test_cast_for_all_literal_types!(Scalar);
