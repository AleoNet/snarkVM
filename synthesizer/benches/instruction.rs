// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#[macro_use]
extern crate criterion;

use console::{
    network::Testnet3,
    program::{Literal, Plaintext, Register, Value, I128, I16, I32, I64, I8, U128, U16, U32, U64, U8},
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

use std::{fmt::Display, str::FromStr};

/// A helper function to construct a set of `FinalizeRegisters` with the given arguments.
pub fn setup_finalize_registers(
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

fn run_benchmark(
    c: &mut Criterion,
    name: impl Display,
    instruction: Instruction<Testnet3>,
    stack: &Stack<Testnet3>,
    benchmarks: &Vec<Vec<Value<Testnet3>>>,
) {
    // Initialize a benchmark group.
    let mut group = c.benchmark_group(name.to_string());
    // For each set of benchmark arguments, bench `evaluate_finalize`.
    for benchmark in benchmarks {
        let benchmark_name =
            format!("{}_{}", name, benchmark.iter().map(|arg| arg.to_string()).collect::<Vec<_>>().join("_"));
        // Initialize a fresh set of finalize registers.
        group.bench_function(&benchmark_name, |b| {
            b.iter_batched(
                || setup_finalize_registers(stack, instruction.to_string(), benchmark),
                |mut finalize_registers| instruction.finalize(stack, &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    }
}

fn bench_arithmetic_instructions(c: &mut Criterion) {
    // Initialize a process.
    let process = Process::<Testnet3>::load().unwrap();
    // Get the stack for the credits program.
    // Note that this is not used for anything other than to satisfy the function signature for `finalize`.
    // This is because `Stack`s are only used in finalize contexts to check that structs are well-formed.
    let stack = process.get_stack("credits.aleo").unwrap();

    macro_rules! bench_instruction {
        // Case 0: Unary operation.
        ($instruction:ident { $( ($input:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 into r1", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!($instruction|$input), instruction, &stack, $args);
            })+
        };
        // Case 1: Binary operation.
        ($instruction:ident { $( ($input_a:ident, $input_b:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 into r2", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!($instruction|$input_a|$input_b), instruction, &stack, $args);
            })+
        };
        // Case 2: Ternary operation.
        ($instruction:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 r2 into r3", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!(<$instruction:lower _ $input_a _ $input_b _ $input_c>), instruction, &stack, $args);
            })+
        };
    }

    let i8_values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I8(I8::new(1i8))))]];
    let i16_values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I16(I16::new(1i16))))]];
    let i32_values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I32(I32::new(1i32))))]];
    let i64_values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I64(I64::new(1i64))))]];
    let i128_values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I128(I128::new(1i128))))]];

    use snarkvm_synthesizer::Abs;
    bench_instruction!(Abs {
        (I8)[i8_values],
        (I16)[i16_values],
        (I32)[i32_values],
        (I64)[i64_values],
        (I128)[i128_values],
    });

    let u8_values = &vec![vec![
        Value::Plaintext(Plaintext::from(Literal::U8(U8::new(1u8)))),
        Value::Plaintext(Plaintext::from(Literal::U8(U8::new(1u8)))),
    ]];
    let u16_values = &vec![vec![
        Value::Plaintext(Plaintext::from(Literal::U16(U16::new(1u16)))),
        Value::Plaintext(Plaintext::from(Literal::U16(U16::new(1u16)))),
    ]];
    let u32_values = &vec![vec![
        Value::Plaintext(Plaintext::from(Literal::U32(U32::new(1u32)))),
        Value::Plaintext(Plaintext::from(Literal::U32(U32::new(1u32)))),
    ]];
    let u64_values = &vec![vec![
        Value::Plaintext(Plaintext::from(Literal::U64(U64::new(1u64)))),
        Value::Plaintext(Plaintext::from(Literal::U64(U64::new(1u64)))),
    ]];
    let u128_values = &vec![vec![
        Value::Plaintext(Plaintext::from(Literal::U128(U128::new(1u128)))),
        Value::Plaintext(Plaintext::from(Literal::U128(U128::new(1u128)))),
    ]];

    use snarkvm_synthesizer::LessThan;
    bench_instruction!(LessThan {
        (U8, U8)[u8_values],
        (U16, U16)[u16_values],
        (U32, U32)[u32_values],
        (U64, U64)[u64_values],
        (U128, U128)[u128_values],
    });

    use snarkvm_synthesizer::And;
    bench_instruction!(And {
        (U8, U8)[u8_values],
        (U16, U16)[u16_values],
        (U32, U32)[u32_values],
        (U64, U64)[u64_values],
        (U128, U128)[u128_values],
    });

    use snarkvm_synthesizer::Or;
    bench_instruction!(Or {
        (U8, U8)[u8_values],
        (U16, U16)[u16_values],
        (U32, U32)[u32_values],
        (U64, U64)[u64_values],
        (U128, U128)[u128_values],
    });

    use snarkvm_synthesizer::Sub;
    bench_instruction!(Sub {
        (U8, U8)[u8_values],
        (U16, U16)[u16_values],
        (U32, U32)[u32_values],
        (U64, U64)[u64_values],
        (U128, U128)[u128_values],
    });

    use snarkvm_synthesizer::Xor;
    bench_instruction!(Xor {
        (U8, U8)[u8_values],
        (U16, U16)[u16_values],
        (U32, U32)[u32_values],
        (U64, U64)[u64_values],
        (U128, U128)[u128_values],
    });
}

criterion_group! {
    name = bench;
    config = Criterion::default().sample_size(10);
    targets = bench_arithmetic_instructions,
}

criterion_main!(bench);
