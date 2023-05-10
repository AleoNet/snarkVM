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
    account::*,
    network::Testnet3,
    program::{Plaintext, Value},
};
use snarkvm_synthesizer::{FinalizeRegisters, FinalizeTypes, Instruction, Process, Program, Stack, Store};

use console::program::{Literal, Register, I8};
use criterion::{BatchSize, Criterion};
use snarkvm_synthesizer::finalize::Finalize;

/// A helper function to construct a set of `FinalizeRegisters` with the given arguments.
pub fn setup_finalize_registers(stack: &Stack<Testnet3>, args: &[Value<Testnet3>]) -> FinalizeRegisters<Testnet3> {
    // Initialize a `Finalize` block with the benchmark arguments as inputs.
    let mut finalize_string = "finalize foo:".to_string();
    for (i, arg) in args.iter().enumerate() {
        finalize_string.push_str(&format!("input r{i} as {};", match arg {
            Value::Plaintext(Plaintext::Literal(literal, _)) => literal.to_type().to_string(),
            _ => panic!("invalid benchmark argument type"),
        }));
    }
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
                || setup_finalize_registers(stack, benchmark),
                |mut finalize_registers| instruction.finalize(stack, &mut finalize_registers).unwrap(),
                BatchSize::PerIteration,
            )
        });
    }
}

fn bench_arithmetic_instructions(c: &mut Criterion) {
    // Initialize a shared stack.
    let stack = Stack::<Testnet3>::new(&Process::load().unwrap(), &Program::credits().unwrap()).unwrap();

    macro_rules! bench_instruction {
        // Case 0: Unary operation.
        ($instruction:ident { $( ($input:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 into r1;", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!(<$instruction:lower _ $input>), instruction, &stack, $args);
            })+
        };
        // Case 1: Binary operation.
        ($instruction:ident { $( ($input_a:ident, $input_b:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 into r2;", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!(<$instruction:lower _ $input_a _ $input_b>), instruction, &stack, $args);
            })+
        };
        // Case 2: Ternary operation.
        ($instruction:ident { $( ($input_a:ident, $input_b:ident, $input_c:ident) [ $args:expr ], )+ }) => {
            $({
                let instruction = Instruction::<Testnet3>::$instruction($instruction::from_str(&format!("{} r0 r1 r2 into r3;", $instruction::<Testnet3>::opcode().to_string())).unwrap());
                run_benchmark(c, stringify!(<$instruction:lower _ $input_a _ $input_b _ $input_c>), instruction, &stack, $args);
            })+
        };
    }

    let values = &vec![vec![Value::Plaintext(Plaintext::from(Literal::I8(I8::new(1i8))))]];

    use snarkvm_synthesizer::Abs;
    bench_instruction!(Abs {
        (I8)[i8_values],
        (I16)[i16_values],
        (I32)[i32_values],
        (I64)[i64_values],
        (I128)[i128_values],
    });
}

criterion_group! {
    name = bench;
    config = Criterion::default().sample_size(10);
    targets = bench_arithmetic_instructions,
}

criterion_main!(bench);
