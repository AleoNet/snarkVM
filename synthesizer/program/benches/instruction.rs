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

#[macro_use]
extern crate criterion;

use anyhow::Result;
use console::{
    network::{Network, Testnet3, TypeName},
    prelude::{TestRng, Uniform, Zero},
    program::{
        Boolean, Field, Group, Identifier, Plaintext, Register, Scalar, Value, I128, I16, I32, I64, I8, U128, U16, U32,
        U64, U8,
    },
};
use snarkvm_synthesizer_program::{CastOperation, Finalize, FinalizeGlobalState, Instruction, RegistersStore};
use synthesizer_process::{FinalizeRegisters, FinalizeTypes, Process, Stack};

use criterion::{BatchSize, Criterion};
use std::{fmt::Display, iter, str::FromStr};

// TODO (d0cd): Add benchmarks using `Address` once random sampling for `Address` is supported.
// TODO (d0cd): Generalize macros to support arbitrary arity instructions (low priority).

macro_rules! bench_instruction {
    // Benchmark a unary instruction, with the given sampling method.
    ($stack:expr, $c:expr, $samples:tt, $instruction:ident { $input:ident , }) => {{
        use snarkvm_synthesizer_program::$instruction;
        let name = concat!(stringify!($instruction), "/", stringify!($input));
        let instruction = Instruction::<Testnet3>::$instruction(
            $instruction::from_str(&format!("{} r0 into r1", $instruction::<Testnet3>::opcode().to_string())).unwrap(),
        );
        $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    let arg = $samples.next().unwrap();
                    setup_finalize_registers(
                        $stack,
                        instruction.to_string(),
                        &[Value::from_str(&arg.to_string()).unwrap()],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    };};
    // Benchmark a unary instruction, with the given sampling method.
    ($stack:expr, $c:expr, $samples:tt, $instruction:ident { $input:ident , }, $as_type:expr) => {{
        use snarkvm_synthesizer_program::$instruction;
        let name = concat!(stringify!($instruction), "/", stringify!($input));
        let instruction = Instruction::<Testnet3>::$instruction(
            $instruction::from_str(&format!(
                "{} r0 into r1 as {}",
                $instruction::<Testnet3>::opcode().to_string(),
                $as_type
            ))
            .unwrap(),
        );
        $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    let arg = $samples.next().unwrap();
                    setup_finalize_registers(
                        $stack,
                        instruction.to_string(),
                        &[Value::from_str(&arg.to_string()).unwrap()],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    };};
    // Benchmark a binary instruction, with the given sampling method.
    ($stack:expr, $c:expr, $samples:tt, $instruction:ident { ($input_a:ident, $input_b:ident) , }) => {{
        use snarkvm_synthesizer_program::$instruction;
        let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
        let instruction = Instruction::<Testnet3>::$instruction(
            $instruction::from_str(&format!("{} r0 r1 into r2", $instruction::<Testnet3>::opcode().to_string()))
                .unwrap(),
        );
        $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    let (first, second) = $samples.next().unwrap();
                    setup_finalize_registers(
                        $stack,
                        instruction.to_string(),
                        &[Value::from_str(&first.to_string()).unwrap(), Value::from_str(&second.to_string()).unwrap()],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    };};
    // Benchmark a ternary instruction, with the given sampling method.
    ($stack:expr, $c:expr, $samples:tt, $instruction:ident { ($input_a:ident, $input_b:ident, $input_c:ident), }) => {{
        use snarkvm_synthesizer_program::$instruction;
        let name = concat!(
            stringify!($instruction),
            "/",
            stringify!($input_a),
            "_",
            stringify!($input_b),
            "_",
            stringify!($input_c)
        );
        let instruction = Instruction::<Testnet3>::$instruction(
            $instruction::from_str(&format!("{} r0 r1 r2 into r3", $instruction::<Testnet3>::opcode().to_string()))
                .unwrap(),
        );
        $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    let (first, second, third) = $samples.next().unwrap();
                    setup_finalize_registers(
                        $stack,
                        instruction.to_string(),
                        &[
                            Value::from_str(&first.to_string()).unwrap(),
                            Value::from_str(&second.to_string()).unwrap(),
                            Value::from_str(&third.to_string()).unwrap(),
                        ],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    }};
    // Benchmark a cast instruction, with the given sampling method.
    ($stack:expr, $c:expr, $samples:tt, $instruction:ident { ($input_a:ident as $input_b:ident), }) => {{
        use snarkvm_synthesizer_program::$instruction;
        let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
        println!("{} {} {}", stringify!($input_a), stringify!($input_b), stringify!($name));
        let instruction = Instruction::<Testnet3>::$instruction(
            $instruction::from_str(&format!(
                "{} r0 into r1 as {}",
                $instruction::<Testnet3>::opcode().to_string(),
                $input_a::<Testnet3>::type_name()
            ))
            .unwrap(),
        );

        $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    let first = $samples.next().unwrap();
                    setup_finalize_registers(
                        $stack,
                        instruction.to_string(),
                        &[Value::from_str(&first.to_string()).unwrap()],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    };};
}

macro_rules! create_nested_array_instruction {
    (Array[$base_type:ident; $length:expr; $nesting:expr]) => {{
        let mut program_block = "".to_string();
        let mut array = "".to_string();
        let mut instruction = "".to_string();
        let base_type = $base_type::<Testnet3>::type_name();

        for i in (0..($nesting + 1)) {
            array = "".to_string();
            instruction = "cast ".to_string();
            (0..$length).for_each(|_| instruction.push_str(&format!("r{} ", i)));
            (0..(i + 1)).for_each(|_| array.push_str(&format!("[")));
            array.push_str(&format!("{};", base_type));
            (0..(i + 1)).for_each(|_| array.push_str(&format!(" {}u32];", $length)));
            instruction.push_str(&format!("into r{} as {}", i + 1, array));
            program_block.push_str(&format!("{}", instruction));
        }
        println!("Program block: {}", program_block);
        println!("Instruction: {}", instruction);
        instruction.pop();
        let instruction = Instruction::<Testnet3>::Cast(CastOperation::<Testnet3, 0>::from_str(&instruction).unwrap());
        println!("Instruction created");
        (program_block, instruction)
    };};
}

macro_rules! bench_cast_array {
    ($stack:expr, $c:expr, $rng:expr, { $( ($input_a:ident as Array[$base_type:ident; $length:expr; $nesting:expr]), )+ }) => {
        $({
            let (program_block, instruction) = create_nested_array_instruction!(Array[$base_type; $length; $nesting]);

            // Benchmark the cast to array operation
            let mut name = concat!("CastArray/{}/Array", stringify!($input_a)).to_string();
            name.push_str(&format!("/Depth{}/Length{}", $nesting, $length));
            println!("Name: {}", name);
            let arg: $input_a<Testnet3> = Uniform::rand($rng);
            $c.bench_function(&format!("{name}/instruction"), |b| {
            b.iter_batched(
                || {
                    setup_finalize_registers(
                        $stack,
                        &program_block,
                        &[Value::from_str(&arg.to_string()).unwrap()],
                    )
                },
                |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
        })*
    };
}

macro_rules! bench_instruction_with_default {
        // Benchmark a unary instruction, using the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt, $instruction:ident { $( $input:ident , )+ }) => {
            $({
                // Define the default sampling method.
                let mut samples = iter::repeat_with(|| {
                    let mut arg: $input::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| arg.$operation())).is_err() {
                        arg = Uniform::rand($rng);
                    }
                    arg
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |arg| arg.$operation(),
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                bench_instruction!($stack, $c, samples, $instruction { $input , });
            })+
        };
        // Benchmark a unary instruction with a question mark (?), using the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt?, $instruction:ident { $( $input:ident , )+ }) => {
            $({
                // Define the default sampling method.
                let mut samples = iter::repeat_with(|| {
                    let mut arg: $input::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| arg.$operation().unwrap())).is_err() {
                        arg = Uniform::rand($rng);
                    }
                    arg
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |arg| arg.$operation().unwrap(),
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                bench_instruction!($stack, $c, samples, $instruction { $input , });
            })+
        };
        // Benchmark a binary instruction, using the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt, $instruction:ident { $( ($input_a:ident, $input_b:ident) , )+ }) => {
            $({
                // Define the default sampling method.
                let mut samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand($rng);
                    let mut second: $input_b::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| first.$operation(&second))).is_err() {
                        first = Uniform::rand($rng);
                        second = Uniform::rand($rng);
                    }
                    (first, second)
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |(first, second)| first.$operation(&second),
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                bench_instruction!($stack, $c, samples, $instruction { ($input_a, $input_b) , });
            })+
        };
        // Benchmark a ternary instruction, with the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt, $instruction:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident), )+ }) => {
            $({
                let mut samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand($rng);
                    let mut second: $input_b::<Testnet3> = Uniform::rand($rng);
                    let mut third: $input_c::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| $input_b::ternary(&first, &second, &third))).is_err() {
                        first = Uniform::rand($rng);
                        second = Uniform::rand($rng);
                        third = Uniform::rand($rng);
                    }
                    (first, second, third)
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_",  stringify!($input_b), "_", stringify!($input_c));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |(first, second, third)| $input_b::ternary(&first, &second, &third),
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                bench_instruction!($stack, $c, samples, $instruction { ($input_a, $input_b, $input_c), });
            })+
        };
        // Benchmark a cast instruction, using the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt, $instruction:ident { $( ($input_a:ident as $input_b:ident), )+ }) => {
            $({
                // Define the default sampling method.
                let mut samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| {
                        let a: Result<$input_b<Testnet3>> = first.cast();
                        a.unwrap();
                    })).is_err() {
                        first = Uniform::rand($rng);
                    }
                    first
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |first| { let a: $input_b<Testnet3> = first.cast().unwrap(); },
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                println!("{} {} {}", stringify!($input_a), stringify!($input_b), format!("{name}/core"));
                bench_instruction!($stack, $c, samples, $instruction { ($input_a as $input_b), });
            })+
        };
        // Benchmark a cast instruction, using the default sampling method.
        ($stack:expr, $c:expr, $rng:expr, $operation:tt, $instruction:ident { $( ($input_a:ident as $), )+ }) => {
            $({
                // Define the default sampling method.
                let mut samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand($rng);
                    while (std::panic::catch_unwind(|| {
                        let a: Result<$input_b<Testnet3>> = first.cast();
                        a.unwrap();
                    })).is_err() {
                        first = Uniform::rand($rng);
                    }
                    first
                });
                // Benchmark the underlying operation.
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
                $c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |first| { let a: $input_b<Testnet3> = first.cast().unwrap(); },
                        BatchSize::SmallInput,
                    )
                });
                // Benchmark the instruction.
                println!("{} {} {}", stringify!($input_a), stringify!($input_b), format!("{name}/core"));
                bench_instruction!($stack, $c, samples, $instruction { ($input_a as $input_b), });
            })+
        };
    }

macro_rules! bench_ped64_commit_instruction {
        ($stack:expr, $c:expr, $rng:expr, $instruction:tt) => {
            let mut samples = iter::repeat_with(|| { (Boolean::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (Boolean, Scalar), });
            let mut samples = iter::repeat_with(|| { (I8::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (I8, Scalar), });
            let mut samples = iter::repeat_with(|| { (I16::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (I16, Scalar), });
            let mut samples = iter::repeat_with(|| { (I32::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (I32, Scalar), });
            let mut samples = iter::repeat_with(|| { (U8::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (U8, Scalar), });
            let mut samples = iter::repeat_with(|| { (U16::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (U16, Scalar), });
            let mut samples = iter::repeat_with(|| { (U32::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (U32, Scalar), });
        }
    }

macro_rules! bench_commit_instruction {
        ($stack:expr, $c:expr, $rng:expr, $instruction:tt) => {
            bench_ped64_commit_instruction!($stack, $c, $rng, $instruction);
            let mut samples = iter::repeat_with(|| { (Field::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (Field, Scalar), });
            let mut samples = iter::repeat_with(|| { (Group::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (Group, Scalar), });
            let mut samples = iter::repeat_with(|| { (I64::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (I64, Scalar), });
            let mut samples = iter::repeat_with(|| { (I128::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (I128, Scalar), });
            let mut samples = iter::repeat_with(|| { (U64::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (U64, Scalar), });
            let mut samples = iter::repeat_with(|| { (U128::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (U128, Scalar), });
            let mut samples = iter::repeat_with(|| { (Scalar::<Testnet3>::rand($rng), Scalar::<Testnet3>::rand($rng)) });
            bench_instruction!($stack, $c, samples, $instruction { (Scalar, Scalar), });
        }
    }

macro_rules! bench_assert {
    ($stack:expr, $c:expr, $rng:expr, $typ:tt) => {
        let mut samples = iter::repeat_with(|| {
            let result = $typ::<Testnet3>::rand($rng);
            (result.clone(), result)
        });
        {
            use snarkvm_synthesizer_program::AssertEq;
            let name = concat!("AssertEq/", stringify!($typ), "_", stringify!($typ));
            let instruction = Instruction::<Testnet3>::AssertEq(
                AssertEq::from_str(&format!("{} r0 r1", AssertEq::<Testnet3>::opcode().to_string())).unwrap(),
            );
            $c.bench_function(&format!("{name}/instruction"), |b| {
                b.iter_batched(
                    || {
                        let (first, second) = samples.next().unwrap();
                        setup_finalize_registers(
                            $stack,
                            instruction.to_string(),
                            &[
                                Value::from_str(&first.to_string()).unwrap(),
                                Value::from_str(&second.to_string()).unwrap(),
                            ],
                        )
                    },
                    |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                    BatchSize::PerIteration,
                )
            });
        };
        let mut samples = iter::repeat_with(|| {
            let first = $typ::<Testnet3>::rand($rng);
            let mut second = $typ::<Testnet3>::rand($rng);
            while first == second {
                second = $typ::<Testnet3>::rand($rng);
            }
            (first, second)
        });
        {
            use snarkvm_synthesizer_program::AssertNeq;
            let name = concat!("AssertNeq/", stringify!($typ), "_", stringify!($typ));
            let instruction = Instruction::<Testnet3>::AssertNeq(
                AssertNeq::from_str(&format!("{} r0 r1", AssertNeq::<Testnet3>::opcode().to_string())).unwrap(),
            );
            $c.bench_function(&format!("{name}/instruction"), |b| {
                b.iter_batched(
                    || {
                        let (first, second) = samples.next().unwrap();
                        setup_finalize_registers(
                            $stack,
                            instruction.to_string(),
                            &[
                                Value::from_str(&first.to_string()).unwrap(),
                                Value::from_str(&second.to_string()).unwrap(),
                            ],
                        )
                    },
                    |mut finalize_registers| instruction.finalize($stack.as_ref(), &mut finalize_registers).unwrap(),
                    BatchSize::PerIteration,
                )
            });
        };
    };
}

/// A helper function to construct a set of `FinalizeRegisters` with the given arguments.
fn setup_finalize_registers(
    stack: &Stack<Testnet3>,
    finalize_body: impl Display,
    args: &[Value<Testnet3>],
) -> FinalizeRegisters<Testnet3> {
    // Initialize a `Finalize` block with the benchmark arguments as inputs.
    let mut finalize_string = "finalize foo:".to_string();
    for (i, arg) in args.iter().enumerate() {
        finalize_string.push_str(&format!(
            "input r{i} as {}.public;",
            match arg {
                Value::Plaintext(Plaintext::Literal(literal, _)) => literal.to_type().to_string(),
                _ => panic!("invalid benchmark argument type"),
            }
        ));
    }
    finalize_string.push_str(&finalize_body.to_string());
    println!("{}", finalize_string);
    let finalize = Finalize::<Testnet3>::from_str(&finalize_string).unwrap();
    // Construct the finalize state.
    let state = FinalizeGlobalState::new::<Testnet3>(0, 0, 0, 0, <Testnet3 as Network>::BlockHash::default()).unwrap();
    // Initialize a fresh set of finalize registers.
    let mut registers = FinalizeRegisters::new(
        state,
        <Testnet3 as Network>::TransitionID::default(),
        Identifier::from_str("test").unwrap(),
        FinalizeTypes::from_finalize(stack, &finalize).unwrap(),
    );
    // Add the arguments into the registers.
    for (i, arg) in args.iter().enumerate() {
        registers.store(stack, &Register::Locator(i as u64), arg.clone()).unwrap();
    }
    registers
}

// ### MATHEMATICAL INSTRUCTIONS ### //

#[rustfmt::skip]
fn abs_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    // Note that this is not used for anything other than to satisfy the function signature for `finalize`.
    // This is because `Stack`s are only used in finalize contexts to check that structs are well-formed.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::prelude::AbsChecked;
    bench_instruction_with_default!(stack, c, rng, abs_checked, Abs { I8, I16, I32, I64, I128, });

    use console::prelude::AbsWrapped;
    bench_instruction_with_default!(stack, c, rng, abs_wrapped, AbsWrapped { I8, I16, I32, I64, I128, });
}

#[rustfmt::skip]
fn bench_arithmetic_add_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();
    
    use std::ops::Add;
    bench_instruction_with_default!(stack, c, rng, add, Add {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::AddWrapped;
    bench_instruction_with_default!(stack, c, rng, add_wrapped, AddWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Div;
    bench_instruction_with_default!(stack, c, rng, div, Div {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::DivWrapped;
    bench_instruction_with_default!(stack, c, rng, div_wrapped, DivWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });
}

#[rustfmt::skip]
fn bench_arithmetic_div_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::prelude::Div;
    bench_instruction_with_default!(stack, c, rng, div, Div {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::DivWrapped;
    bench_instruction_with_default!(stack, c, rng, div_wrapped, DivWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Double;
    bench_instruction_with_default!(stack, c, rng, double, Double { Field, Group, });

    use core::ops::Mul;
    bench_instruction_with_default!(stack, c, rng, mul, Mul {
        (Field, Field),
        (Group, Scalar),
        (Scalar, Group),
    });

    // Use a custom sampling method for integer multiplication, since there is a high chance of overflow.
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), I8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I8, I8), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), I16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I16, I16), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), I32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I32, I32), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), I64::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I64, I64), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), I128::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I128, I128), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U8, U8), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U16, U16), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U32, U32), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U64::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U64, U64), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U128::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U128, U128), });

    use console::prelude::MulWrapped;
    bench_instruction_with_default!(stack, c, rng, mul_wrapped, MulWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Inverse;
    bench_instruction_with_default!(stack, c, rng, inverse?, Inv { Field, });

    use core::ops::Neg;
    bench_instruction_with_default!(stack, c, rng, neg, Neg { Field, Group, I8, I16, I32, I64, I128, });

    use console::prelude::Sub;
    bench_instruction_with_default!(stack, c, rng, sub, Sub {
        (Field, Field),
        (Group, Group),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::SubWrapped;
    bench_instruction_with_default!(stack, c, rng, sub_wrapped, SubWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });
}

#[rustfmt::skip]
fn bench_arithmetic_mul_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();
    
    use console::prelude::Double;
    bench_instruction_with_default!(stack, c, rng, double, Double { Field, Group, });

    use core::ops::Mul;
    bench_instruction_with_default!(stack, c, rng, mul, Mul {
        (Field, Field),
        (Group, Scalar),
        (Scalar, Group),
    });

    // Use a custom sampling method for integer multiplication, since there is a high chance of overflow.
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), I8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I8, I8), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), I16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I16, I16), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), I32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I32, I32), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), I64::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I64, I64), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), I128::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (I128, I128), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U8, U8), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U16, U16), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U32, U32), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U64::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U64, U64), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U128::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Mul { (U128, U128), });

    use console::prelude::MulWrapped;
    bench_instruction_with_default!(stack, c, rng, mul_wrapped, MulWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Inverse;
    bench_instruction_with_default!(stack, c, rng, inverse?, Inv { Field, });

    use core::ops::Neg;
    bench_instruction_with_default!(stack, c, rng, neg, Neg { Field, Group, I8, I16, I32, I64, I128, });

    use console::prelude::Sub;
    bench_instruction_with_default!(stack, c, rng, sub, Sub {
        (Field, Field),
        (Group, Group),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::SubWrapped;
    bench_instruction_with_default!(stack, c, rng, sub_wrapped, SubWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });
}

#[rustfmt::skip]
fn bench_arithmetic_neg_and_sub_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::prelude::Inverse;
    bench_instruction_with_default!(stack, c, rng, inverse?, Inv { Field, });

    use core::ops::Neg;
    bench_instruction_with_default!(stack, c, rng, neg, Neg { Field, Group, I8, I16, I32, I64, I128, });

    use console::prelude::Sub;
    bench_instruction_with_default!(stack, c, rng, sub, Sub {
        (Field, Field),
        (Group, Group),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::SubWrapped;
    bench_instruction_with_default!(stack, c, rng, sub_wrapped, SubWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });
}

#[rustfmt::skip]
fn bench_cast_instruction(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::program::Cast;
    bench_instruction_with_default!(stack, c, rng, cast, Cast {
        (I8 as I16),
        (I8 as I32),
        (I8 as I64),
        (I8 as I128),
        (I8 as U8),
        (I8 as U16),
        (I8 as U32),
        (I8 as U64),
        (I8 as U128),
        (I16 as I32),
        (I16 as I64),
        (I16 as I128),
        (I16 as U32),
        (I16 as U64),
        (I16 as U128),
        (I32 as I64),
        (I32 as I128),
        (I32 as U64),
        (I32 as U128),
        (I64 as I128),
        (I64 as U128),
        (U8 as I8),
        (U8 as I16),
        (U8 as I32),
        (U8 as I64),
        (U8 as I128),
        (U8 as U16),
        (U8 as U32),
        (U8 as U64),
        (U8 as U128),
        (U16 as I16),
        (U16 as I32),
        (U16 as I64),
        (U16 as I128),
        (U16 as U32),
        (U16 as U64),
        (U16 as U128),
        (U32 as I32),
        (U32 as I64),
        (U32 as I128),
        (U32 as U64),
        (U32 as U128),
        (U64 as I64),
        (U64 as I128),
        (U64 as U128),
        (U128 as I128),
        (I8 as Field),
        (I16 as Field),
        (I32 as Field),
        (I64 as Field),
        (I128 as Field),
        (U8 as Field),
        (U16 as Field),
        (U32 as Field),
        (U64 as Field),
        (U128 as Field),
        (Field as Group),
    });

    bench_cast_array!(stack, c, rng, { 
        (I16 as Array[I16; 2; 0]),
        (I16 as Array[I16; 2; 1]),
    });
}

#[rustfmt::skip]
fn bench_power_and_remainder_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::prelude::Modulo;
    bench_instruction_with_default!(stack, c, rng, modulo, Modulo {
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Pow;
    bench_instruction_with_default!(stack, c, rng, pow, Pow {
        (Field, Field),
    });
    // Use a custom sampling method for integer exponentiation, since there is a high chance of overflow.
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I8, U8), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I8, U16), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I8, U32), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I16, U8), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I16, U16), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I16, U32), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I32, U8), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I32, U16), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I32, U32), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I64, U8), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I64, U16), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I64, U32), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I128, U8), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I128, U16), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (I128, U32), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U8, U8), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U8, U16), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U8, U32), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U16, U8), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U16, U16), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U16, U32), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U32, U8), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U32, U16), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U32, U32), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U64, U8), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U64, U16), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U64, U32), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U128, U8), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U128, U16), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Pow { (U128, U32), });

    use console::prelude::PowWrapped;
    bench_instruction_with_default!(stack, c, rng, pow_wrapped, PowWrapped {
        (I8, U8),
        (I8, U16),
        (I8, U32),
        (I16, U8),
        (I16, U16),
        (I16, U32),
        (I32, U8),
        (I32, U16),
        (I32, U32),
        (I64, U8),
        (I64, U16),
        (I64, U32),
        (I128, U8),
        (I128, U16),
        (I128, U32),
        (U8, U8),
        (U8, U16),
        (U8, U32),
        (U16, U8),
        (U16, U16),
        (U16, U32),
        (U32, U8),
        (U32, U16),
        (U32, U32),
        (U64, U8),
        (U64, U16),
        (U64, U32),
        (U128, U8),
        (U128, U16),
        (U128, U32),
    });

    use core::ops::Rem;
    bench_instruction_with_default!(stack, c, rng, rem, Rem {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::RemWrapped;
    bench_instruction_with_default!(stack, c, rng, rem_wrapped, RemWrapped {
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Square;
    bench_instruction_with_default!(stack, c, rng, square, Square { Field, });

    use console::prelude::SquareRoot;
    bench_instruction_with_default!(stack, c, rng, square_root?, SquareRoot { Field, });
}

// ### BIT SHIFT INSTRUCTIONS ### //

#[rustfmt::skip]
fn bench_shift_left_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    // Use a custom sampling method for left-shift, since there is a high chance of overflow.
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I8, U8), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I8, U16), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I8, U32), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I16, U8), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I16, U16), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I16, U32), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I32, U8), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I32, U16), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I32, U32), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I64, U8), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I64, U16), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I64, U32), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I128, U8), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I128, U16), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (I128, U32), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U8, U8), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U8, U16), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U8, U32), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U16, U8), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U16, U16), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U16, U32), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U32, U8), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U32, U16), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U32, U32), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U64, U8), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U64, U16), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U64, U32), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U128, U8), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U128, U16), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shl { (U128, U32), });

    use console::prelude::ShlWrapped;
    bench_instruction_with_default!(stack, c, rng, shl_wrapped, ShlWrapped {
        (I8, U8),
        (I8, U16),
        (I8, U32),
        (I16, U8),
        (I16, U16),
        (I16, U32),
        (I32, U8),
        (I32, U16),
        (I32, U32),
        (I64, U8),
        (I64, U16),
        (I64, U32),
        (I128, U8),
        (I128, U16),
        (I128, U32),
        (U8, U8),
        (U8, U16),
        (U8, U32),
        (U16, U8),
        (U16, U16),
        (U16, U32),
        (U32, U8),
        (U32, U16),
        (U32, U32),
        (U64, U8),
        (U64, U16),
        (U64, U32),
        (U128, U8),
        (U128, U16),
        (U128, U32),
    });
}

#[rustfmt::skip]
fn bench_shift_right_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    // Use a custom sampling method for left-shift, since there is a high chance of overflow.
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I8, U8), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I8, U16), });
    let mut samples = iter::repeat((I8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I8, U32), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I16, U8), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I16, U16), });
    let mut samples = iter::repeat((I16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I16, U32), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I32, U8), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I32, U16), });
    let mut samples = iter::repeat((I32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I32, U32), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I64, U8), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I64, U16), });
    let mut samples = iter::repeat((I64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I64, U32), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I128, U8), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I128, U16), });
    let mut samples = iter::repeat((I128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (I128, U32), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U8, U8), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U8, U16), });
    let mut samples = iter::repeat((U8::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U8, U32), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U16, U8), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U16, U16), });
    let mut samples = iter::repeat((U16::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U16, U32), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U32, U8), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U32, U16), });
    let mut samples = iter::repeat((U32::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U32, U32), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U64, U8), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U64, U16), });
    let mut samples = iter::repeat((U64::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U64, U32), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U8::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U128, U8), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U16::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U128, U16), });
    let mut samples = iter::repeat((U128::<Testnet3>::zero(), U32::<Testnet3>::zero()));
    bench_instruction!(stack, c, samples, Shr { (U128, U32), });

    use console::prelude::ShrWrapped;
    bench_instruction_with_default!(stack, c, rng, shr_wrapped, ShrWrapped {
        (I8, U8),
        (I8, U16),
        (I8, U32),
        (I16, U8),
        (I16, U16),
        (I16, U32),
        (I32, U8),
        (I32, U16),
        (I32, U32),
        (I64, U8),
        (I64, U16),
        (I64, U32),
        (I128, U8),
        (I128, U16),
        (I128, U32),
        (U8, U8),
        (U8, U16),
        (U8, U32),
        (U16, U8),
        (U16, U16),
        (U16, U32),
        (U32, U8),
        (U32, U16),
        (U32, U32),
        (U64, U8),
        (U64, U16),
        (U64, U32),
        (U128, U8),
        (U128, U16),
        (U128, U32),
    });
}

// ### LOGICAL INSTRUCTIONS ### //

#[rustfmt::skip]
fn bench_assert_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    bench_assert!(stack, c, rng, Boolean);
    bench_assert!(stack, c, rng, Field);
    bench_assert!(stack, c, rng, Group);
    bench_assert!(stack, c, rng, I8);
    bench_assert!(stack, c, rng, I16);
    bench_assert!(stack, c, rng, I32);
    bench_assert!(stack, c, rng, I64);
    bench_assert!(stack, c, rng, I128);
    bench_assert!(stack, c, rng, Scalar);
    bench_assert!(stack, c, rng, U8);
    bench_assert!(stack, c, rng, U16);
    bench_assert!(stack, c, rng, U32);
    bench_assert!(stack, c, rng, U64);
    bench_assert!(stack, c, rng, U128);
}

#[rustfmt::skip]
fn bench_equality_comparison_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    // Note that this is not used for anything other than to satisfy the function signature for `finalize`.
    // This is because `Stack`s are only used in finalize contexts to check that structs are well-formed.
    let stack = process.get_stack("credits.aleo").unwrap();

    let mut samples = iter::repeat_with(|| { (Boolean::<Testnet3>::rand(rng), Boolean::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (Boolean, Boolean), });
    bench_instruction!(stack, c, samples, IsNeq { (Boolean, Boolean), });
    let mut samples = iter::repeat_with(|| { (Field::<Testnet3>::rand(rng), Field::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (Field, Field), });
    bench_instruction!(stack, c, samples, IsNeq { (Field, Field), });
    let mut samples = iter::repeat_with(|| { (Group::<Testnet3>::rand(rng), Group::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (Group, Group), });
    bench_instruction!(stack, c, samples, IsNeq { (Group, Group), });
    let mut samples = iter::repeat_with(|| { (I8::<Testnet3>::rand(rng), I8::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (I8, I8), });
    bench_instruction!(stack, c, samples, IsNeq { (I8, I8), });
    let mut samples = iter::repeat_with(|| { (I16::<Testnet3>::rand(rng), I16::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (I16, I16), });
    bench_instruction!(stack, c, samples, IsNeq { (I16, I16), });
    let mut samples = iter::repeat_with(|| { (I32::<Testnet3>::rand(rng), I32::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (I32, I32), });
    bench_instruction!(stack, c, samples, IsNeq { (I32, I32), });
    let mut samples = iter::repeat_with(|| { (I64::<Testnet3>::rand(rng), I64::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (I64, I64), });
    bench_instruction!(stack, c, samples, IsNeq { (I64, I64), });
    let mut samples = iter::repeat_with(|| { (I128::<Testnet3>::rand(rng), I128::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (I128, I128), });
    bench_instruction!(stack, c, samples, IsNeq { (I128, I128), });
    let mut samples = iter::repeat_with(|| { (Scalar::<Testnet3>::rand(rng), Scalar::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (Scalar, Scalar), });
    bench_instruction!(stack, c, samples, IsNeq { (Scalar, Scalar), });
    let mut samples = iter::repeat_with(|| { (U8::<Testnet3>::rand(rng), U8::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (U8, U8), });
    bench_instruction!(stack, c, samples, IsNeq { (U8, U8), });
    let mut samples = iter::repeat_with(|| { (U16::<Testnet3>::rand(rng), U16::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (U16, U16), });
    bench_instruction!(stack, c, samples, IsNeq { (U16, U16), });
    let mut samples = iter::repeat_with(|| { (U32::<Testnet3>::rand(rng), U32::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (U32, U32), });
    bench_instruction!(stack, c, samples, IsNeq { (U32, U32), });
    let mut samples = iter::repeat_with(|| { (U64::<Testnet3>::rand(rng), U64::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (U64, U64), });
    bench_instruction!(stack, c, samples, IsNeq { (U64, U64), });
    let mut samples = iter::repeat_with(|| { (U128::<Testnet3>::rand(rng), U128::<Testnet3>::rand(rng)) });
    bench_instruction!(stack, c, samples, IsEq { (U128, U128), });
    bench_instruction!(stack, c, samples, IsNeq { (U128, U128), });
}

#[rustfmt::skip]
fn bench_logical_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use core::ops::BitAnd;
    bench_instruction_with_default!(stack, c, rng, bitand, And {
        (Boolean, Boolean),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use console::prelude::Nand;
    bench_instruction_with_default!(stack, c, rng, nand, Nand {
        (Boolean, Boolean),
    });

    use console::prelude::Nor;
    bench_instruction_with_default!(stack, c, rng, nor, Nor {
        (Boolean, Boolean),
    });

    use core::ops::Not;
    bench_instruction_with_default!(stack, c, rng, not, Not { Boolean, I8, I16, I32, I64, I128, U8, U16, U32, U64, });

    use core::ops::BitOr;
    bench_instruction_with_default!(stack, c, rng, bitor, Or {
        (Boolean, Boolean),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
    });
}

#[rustfmt::skip]
fn bench_set_operations(c: &mut Criterion) {
    
}

#[rustfmt::skip]
fn bench_order_comparison_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    // Note that this is not used for anything other than to satisfy the function signature for `finalize`.
    // This is because `Stack`s are only used in finalize contexts to check that structs are well-formed.
    let stack = process.get_stack("credits.aleo").unwrap();

    bench_instruction_with_default!(stack, c, rng, is_less_than, LessThan {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
        (Scalar, Scalar),
    });

    bench_instruction_with_default!(stack, c, rng, is_less_than_or_equal, LessThanOrEqual {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
        (Scalar, Scalar),
    });
    
    use console::prelude::Compare;
    bench_instruction_with_default!(stack, c, rng, is_greater_than, GreaterThan {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
        (Scalar, Scalar),
    });

    bench_instruction_with_default!(stack, c, rng, is_greater_than_or_equal, GreaterThanOrEqual {
        (Field, Field),
        (I8, I8),
        (I16, I16),
        (I32, I32),
        (I64, I64),
        (I128, I128),
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
        (Scalar, Scalar),
    });
}

#[rustfmt::skip]
fn bench_ternary_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    use console::prelude::Ternary;
    bench_instruction_with_default!(stack, c, rng, ternary, Ternary {
        // (Boolean, Address, Address),
        (Boolean, Boolean, Boolean),
        (Boolean, Field, Field),
        (Boolean, Group, Group),
        (Boolean, I8, I8),
        (Boolean, I16, I16),
        (Boolean, I32, I32),
        (Boolean, I64, I64),
        (Boolean, I128, I128),
        (Boolean, U8, U8),
        (Boolean, U16, U16),
        (Boolean, U32, U32),
        (Boolean, U64, U64),
        (Boolean, U128, U128),
        (Boolean, Scalar, Scalar),
    });
}

// ### HASH INSTRUCTIONS ### //

#[rustfmt::skip]
fn bench_bhp_commit_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();
    
    // bench_commit_instruction!(stack, c, rng, CommitBHP256);
    // bench_commit_instruction!(stack, c, rng, CommitBHP512);
    // bench_commit_instruction!(stack, c, rng, CommitBHP768);
    // bench_commit_instruction!(stack, c, rng, CommitBHP1024);
}

#[rustfmt::skip]
fn bench_poseidon_commit_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();
    
    // bench_ped64_commit_instruction!(stack, c, rng, CommitPED64);
    // bench_ped64_commit_instruction!(stack, c, rng, CommitPED128);
    // let mut samples = iter::repeat_with(|| { (I64::<Testnet3>::rand(rng), Scalar::<Testnet3>::rand(rng)) });
    // bench_instruction!(stack, c, samples, CommitPED128 { (I64, Scalar), });
    // let mut samples = iter::repeat_with(|| { (U64::<Testnet3>::rand(rng), Scalar::<Testnet3>::rand(rng)) });
    // bench_instruction!(stack, c, samples, CommitPED128 { (U64, Scalar), });
}

#[rustfmt::skip]
fn bench_hash_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    let stack = process.get_stack("credits.aleo").unwrap();

    macro_rules! bench_ped64_hash_instruction {
        ($stack:expr, $c:expr, $rng:expr, $instruction:tt) => {
            let mut samples = iter::repeat_with(|| { Boolean::<Testnet3>::rand($rng) });
            bench_instruction!($stack, $c, samples, $instruction { Boolean, }, "group");
            let mut samples = iter::repeat_with(|| { I8::<Testnet3>::rand($rng) });
            bench_instruction!($stack, $c, samples, $instruction { I8, }, "group");
            let mut samples = iter::repeat_with(|| { I16::<Testnet3>::rand($rng) });
            bench_instruction!($stack, $c, samples, $instruction { I16, }, "group");
            let mut samples = iter::repeat_with(|| { I32::<Testnet3>::rand($rng) });
            bench_instruction!($stack, $c, samples, $instruction { I32, }, "group");
            let mut samples = iter::repeat_with(|| { U8::<Testnet3>::rand($rng) });
            bench_instruction!($stack, $c, samples, $instruction { U8, }, "group");
            let mut samples = iter::repeat_with(|| { U16::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { U16, }, "group");
            let mut samples = iter::repeat_with(|| { U32::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { U32, }, "group");
        }
    }

    macro_rules! bench_hash_instruction {
        ($stack:expr, $c:expr, $rng:expr, $instruction:tt) => {
            bench_ped64_hash_instruction!($stack, $c, $rng, $instruction);
            let mut samples = iter::repeat_with(|| { Field::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { Field, }, "group");
            let mut samples = iter::repeat_with(|| { Group::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { Group, }, "group");
            let mut samples = iter::repeat_with(|| { I64::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { I64, }, "group");
            let mut samples = iter::repeat_with(|| { I128::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { I128, }, "group");
            let mut samples = iter::repeat_with(|| { U64::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { U64, }, "group");
            let mut samples = iter::repeat_with(|| { U128::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { U128, }, "group");
            let mut samples = iter::repeat_with(|| { Scalar::<Testnet3>::rand(rng) });
            bench_instruction!($stack, $c, samples, $instruction { Scalar, }, "group");
        }
    }

    bench_hash_instruction!(stack, c, rng, HashBHP256);
    bench_hash_instruction!(stack, c, rng, HashBHP512);
    bench_hash_instruction!(stack, c, rng, HashBHP768);
    bench_hash_instruction!(stack, c, rng, HashBHP1024);

    bench_ped64_hash_instruction!(stack, c, rng, HashPED64);
    bench_ped64_hash_instruction!(stack, c, rng, HashPED128);
    let mut samples = iter::repeat_with(|| { I64::<Testnet3>::rand(rng) });
    bench_instruction!(stack, c, samples, HashPED128 { I64, }, "group");
    let mut samples = iter::repeat_with(|| { U64::<Testnet3>::rand(rng) });
    bench_instruction!(stack, c, samples, HashPED128 { U64, }, "group");

    bench_hash_instruction!(stack, c, rng, HashPSD2);
    bench_hash_instruction!(stack, c, rng, HashPSD4);
    bench_hash_instruction!(stack, c, rng, HashPSD8);
    
    
    
}

// Create the benchmark group.
criterion_group! {
    name = bench;
    config = Criterion::default().sample_size(100);
    targets = abs_instructions, bench_arithmetic_add_instructions, bench_arithmetic_div_instructions, bench_arithmetic_mul_instructions, bench_arithmetic_neg_and_sub_instructions, bench_assert_instructions, bench_bhp_commit_instructions, bench_cast_instruction, bench_equality_comparison_instructions, bench_hash_instructions, bench_logical_instructions, bench_order_comparison_instructions, bench_poseidon_commit_instructions, bench_power_and_remainder_instructions, bench_shift_left_instructions, bench_shift_right_instructions, bench_ternary_instructions,
}

criterion_main!(bench);
