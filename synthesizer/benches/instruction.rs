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

use console::{
    network::Testnet3,
    prelude::Uniform,
    program::{
        Boolean,
        Field,
        Group,
        Plaintext,
        Register,
        Scalar,
        Value,
        I128,
        I16,
        I32,
        I64,
        I8,
        U128,
        U16,
        U32,
        U64,
        U8,
    },
};
use criterion::{BatchSize, Criterion};
use snarkvm_synthesizer::{
    finalize::Finalize,
    FinalizeRegisters,
    FinalizeTypes,
    Instruction,
    Process,
    RegistersStore,
    Stack,
};

use snarkvm_utilities::TestRng;
use std::{iter, fmt::Display, str::FromStr};

/// A helper function to construct a set of `FinalizeRegisters` with the given arguments.
fn setup_finalize_registers(
    stack: &Stack<Testnet3>,
    finalize_body: impl Display,
    args: &[Value<Testnet3>],
) -> FinalizeRegisters<Testnet3> {
    // Initialize a `Finalize` block with the benchmark arguments as inputs.
    let mut finalize_string = "finalize foo:".to_string();
    for (i, arg) in args.iter().enumerate() {
        finalize_string.push_str(&format!("input r{i} as {}.public;", match arg {
            Value::Plaintext(Plaintext::Literal(literal, _)) => literal.to_type().to_string(),
            _ => panic!("invalid benchmark argument type"),
        }));
    }
    finalize_string.push_str(&finalize_body.to_string());
    let finalize = Finalize::<Testnet3>::from_str(&finalize_string).unwrap();
    // Initialize a fresh set of finalize registers.
    let mut registers = FinalizeRegisters::new(FinalizeTypes::from_finalize(stack, &finalize).unwrap());
    // Add the arguments into the registers.
    for (i, arg) in args.iter().enumerate() {
        registers.store(stack, &Register::Locator(i as u64), arg.clone()).unwrap();
    }
    registers
}

fn bench_arithmetic_instructions(c: &mut Criterion) {
    // Initialize an RNG.
    let rng = &mut TestRng::default();
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    // Note that this is not used for anything other than to satisfy the function signature for `finalize`.
    // This is because `Stack`s are only used in finalize contexts to check that structs are well-formed.
    let stack = process.get_stack("credits.aleo").unwrap();

    macro_rules! bench_instruction {
        // Case 0: Unary operation.
        ($operation:ident, $instruction:ident { $( $input:ident , )+ }) => {
            $({
                let name = concat!(stringify!($instruction), "/", stringify!($input));
                let samples = iter::repeat_with(|| {
                    let mut arg: $input::<Testnet3> = Uniform::rand(rng);
                    while (std::panic::catch_unwind(|| arg.$operation())).is_err() {
                        arg = Uniform::rand(rng);
                    }
                    arg
                });
                // Benchmark the core operation of the instruction.
                c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |arg| arg.$operation(),
                        BatchSize::PerIteration,
                    )
                });
                // Benchmark the entire instruction.
                use snarkvm_synthesizer::$instruction;
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 into r1", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                c.bench_function(&format!("{name}/instruction"), |b| {
                    b.iter_batched(
                        || {
                            let arg = samples.next().unwrap();
                            setup_finalize_registers(stack, instruction.to_string(), &[Value::from_str(&arg.to_string()).unwrap()])
                        },
                        |mut finalize_registers| instruction.finalize(stack, &mut finalize_registers).unwrap(),
                        BatchSize::PerIteration,
                    )
                });
            })+
        };
        // Case 1: Binary operation.
        ($operation:ident, $instruction:ident { $( ($input_a:ident, $input_b:ident) , )+ }) => {
            $({
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_", stringify!($input_b));
                let samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand(rng);
                    let mut second: $input_b::<Testnet3> = Uniform::rand(rng);
                    while (std::panic::catch_unwind(|| first.$operation(&second))).is_err() {
                        first = Uniform::rand(rng);
                        second = Uniform::rand(rng);
                    }
                    (first, second)
                });
                // Benchmark the core operation of the instruction.
                c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |(first, second)| first.$operation(&second),
                        BatchSize::PerIteration,
                    )
                });
                // Benchmark the entire instruction.
                use snarkvm_synthesizer::$instruction;
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 into r2", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                c.bench_function(&format!("{name}/instruction"), |b| {
                    b.iter_batched(
                        || {
                            let (first, second) = samples.next().unwrap();
                            setup_finalize_registers(stack, instruction.to_string(), &[Value::from_str(&first.to_string()).unwrap(), Value::from_str(&second.to_string()).unwrap()])
                        },
                        |mut finalize_registers| instruction.finalize(stack, &mut finalize_registers).unwrap(),
                        BatchSize::PerIteration,
                    )
                });
            })+
        };
        // Case 2: Ternary operation.
        ($operation:ident, $instruction:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident), )+ }) => {
            $({
                let name = concat!(stringify!($instruction), "/", stringify!($input_a), "_",  stringify!($input_b), "_", stringify!($input_c));
                let samples = iter::repeat_with(|| {
                    let mut first: $input_a::<Testnet3> = Uniform::rand(rng);
                    let mut second: $input_b::<Testnet3> = Uniform::rand(rng);
                    let mut third: $input_c::<Testnet3> = Uniform::rand(rng);
                    while (std::panic::catch_unwind(|| $input_b::ternary(&first, &second, &third))).is_err() {
                        first = Uniform::rand(rng);
                        second = Uniform::rand(rng);
                        third = Uniform::rand(rng);
                    }
                    (first, second, third)
                });
                // Benchmark the core operation of the instruction.
                c.bench_function(&format!("{name}/core"), |b| {
                    b.iter_batched(
                        || samples.next().unwrap(),
                        |(first, second, third)| $input_b::ternary(&first, &second, &third),
                        BatchSize::PerIteration
                    )
                });
                // Benchmark the entire instruction.
                use snarkvm_synthesizer::$instruction;
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 r2 into r3", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                c.bench_function(&format!("{name}/instruction"), |b| {
                    b.iter_batched(
                        || {
                            let (first, second, third) = samples.next().unwrap();
                            setup_finalize_registers(stack, instruction.to_string(), &[Value::from_str(&first.to_string()).unwrap(), Value::from_str(&second.to_string()).unwrap(), Value::from_str(&third.to_string()).unwrap()])
                        },
                        |mut finalize_registers| instruction.finalize(stack, &mut finalize_registers).unwrap(),
                        BatchSize::PerIteration
                    )
                });
            })+
        };
    }

    use console::prelude::AbsChecked;
    bench_instruction!(abs_checked, Abs { I8, I16, I32, I64, I128, });

    use console::prelude::AbsWrapped;
    bench_instruction!(abs_wrapped, AbsWrapped { I8, I16, I32, I64, I128, });

    use std::ops::Add;
    bench_instruction!(add, Add {
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
    bench_instruction!(add_wrapped, AddWrapped {
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

    use core::ops::BitAnd;
    bench_instruction!(bitand, And {
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

    use console::prelude::Div;
    bench_instruction!(div, Div {
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
    bench_instruction!(div_wrapped, DivWrapped {
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
    bench_instruction!(double, Double { Field, Group, });

    use console::prelude::Compare;
    bench_instruction!(is_greater_than, GreaterThan {
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

    bench_instruction!(is_greater_than_or_equal, GreaterThanOrEqual {
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

    use console::prelude::Inverse;
    bench_instruction!(inverse, Inv { Field, });

    bench_instruction!(is_less_than, LessThan {
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

    bench_instruction!(is_less_than_or_equal, LessThanOrEqual {
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

    use console::prelude::Modulo;
    bench_instruction!(modulo, Modulo {
        (U8, U8),
        (U16, U16),
        (U32, U32),
        (U64, U64),
        (U128, U128),
    });

    use core::ops::Mul;
    bench_instruction!(mul, Mul {
        (Field, Field),
        (Group, Scalar),
        (Scalar, Group),
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

    use console::prelude::MulWrapped;
    bench_instruction!(mul_wrapped, MulWrapped {
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
    bench_instruction!(nand, Nand {
        (Boolean, Boolean),
    });

    use core::ops::Neg;
    bench_instruction!(neg, Neg { Field, Group, I8, I16, I32, I64, I128, });

    use console::prelude::Nor;
    bench_instruction!(nor, Nor {
        (Boolean, Boolean),
    });

    use core::ops::Not;
    bench_instruction!(not, Not { Boolean, I8, I16, I32, I64, I128, U8, U16, U32, U64, });

    use core::ops::BitOr;
    bench_instruction!(bitor, Or {
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

    use console::prelude::Pow;
    bench_instruction!(pow, Pow {
        (Field, Field),
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

    use console::prelude::PowWrapped;
    bench_instruction!(pow_wrapped, PowWrapped {
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
    bench_instruction!(rem, Rem {
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
    bench_instruction!(rem_wrapped, RemWrapped {
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

    use console::prelude::ShlChecked;
    bench_instruction!(shl_checked, Shl {
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

    use console::prelude::ShlWrapped;
    bench_instruction!(shl_wrapped, ShlWrapped {
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

    use console::prelude::ShrChecked;
    bench_instruction!(shr_checked, Shr {
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

    use console::prelude::ShrWrapped;
    bench_instruction!(shr_wrapped, ShrWrapped {
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

    use console::prelude::Square;
    bench_instruction!(square, Square { Field, });

    use console::prelude::SquareRoot;
    bench_instruction!(square_root, SquareRoot { Field, });

    use std::ops::Sub;
    bench_instruction!(sub, Sub {
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
    bench_instruction!(sub_wrapped, SubWrapped {
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

    use console::prelude::Ternary;
    bench_instruction!(ternary, Ternary {
        // (Boolean, Address, Address), // TODO (d0cd): Enable this when we have a way to generate random addresses via `Uniform::rand`.
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

criterion_group! {
    name = bench;
    config = Criterion::default().sample_size(10);
    targets = bench_arithmetic_instructions,
}

criterion_main!(bench);
