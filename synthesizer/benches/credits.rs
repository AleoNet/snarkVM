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

// #[macro_use]
// extern crate criterion;
//
// mod utilities;
// use utilities::*;
//
// use console::{
//     network::Testnet3,
//     program::{Address, Identifier, Literal, One, Plaintext, ProgramID, Value},
// };
//
// use snarkvm_synthesizer::Program;
// use snarkvm_utilities::{TestRng, Uniform};
//
// use criterion::Criterion;
// use std::str::FromStr;
//
// // Note: The number of commands that can be included in a finalize block must be within the range [1, 255].
// const NUM_EXECUTIONS: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 256];
//
// fn program() -> Program<Testnet3> {
//     Program::from_str(
//         r"
// program test.aleo;
//
// record credits:
//     owner as address.private;
//     gates as u64.private;
//
// mapping account:
//     key left as address.public;
//     value right as u64.public;
//
// function mint_private:
//     input r0 as address.private;
//     input r1 as u64.private;
//     cast r0 r1 into r2 as credits.record;
//     output r2 as credits.record;
//
// function mint_public:
//     input r0 as address.public;
//     input r1 as u64.public;
//     finalize r0 r1;
//
// finalize mint_public:
//     input r0 as address.public;
//     input r1 as u64.public;
//     get.or_init account[r0] 0u64 into r2;
//     add r2 r1 into r3;
//     set r3 into account[r0];
//
// function transfer_public:
//     input r0 as address.public;
//     input r1 as u64.public;
//     finalize self.caller r0 r1;
//
// finalize transfer_public:
//     input r0 as address.public;
//     input r1 as address.public;
//     input r2 as u64.public;
//     get.or_init account[r0] 0u64 into r3;
//     sub r3 r2 into r4;
//     set r4 into account[r0];
//     get.or_init account[r1] 0u64 into r5;
//     add r5 r2 into r6;
//     set r6 into account[r1];
//
// function transfer_private_to_public:
//     input r0 as credits.record;
//     input r1 as address.public;
//     input r2 as u64.public;
//     sub r0.gates r2 into r3;
//     cast r0.owner r3 into r4 as credits.record;
//     output r4 as credits.record;
//     finalize r1 r2;
//
// finalize transfer_private_to_public:
//     input r0 as address.public;
//     input r1 as u64.public;
//     get.or_init account[r0] 0u64 into r2;
//     add r2 r1 into r3;
//     set r3 into account[r0];
//
// function transfer_public_to_private:
//     input r0 as address.public;
//     input r1 as u64.public;
//     cast r0 r1 into r2 as credits.record;
//     output r2 as credits.record;
//     finalize self.caller r1;
//
// finalize transfer_public_to_private:
//     input r0 as address.public;
//     input r1 as u64.public;
//     get.or_init account[r0] 0u64 into r2;
//     sub r2 r1 into r3;
//     set r3 into account[r0];
//
// function split:
//     input r0 as credits.record;
//     input r1 as u64.private;
//     sub r0.gates r1 into r2;
//     cast r0.owner r1 into r3 as credits.record;
//     cast r0.owner r2 into r4 as credits.record;
//     output r3 as credits.record;
//     output r4 as credits.record;
// ",
//     )
//     .unwrap()
// }
//
// #[cfg(feature = "test-utilities")]
// fn bench_mint_public(c: &mut Criterion) {
//     let rng = &mut TestRng::default();
//
//     let address = Value::Plaintext(Plaintext::from(Literal::Address(Address::new(Uniform::rand(rng)))));
//     let amount = Value::Plaintext(Plaintext::from(Literal::U64(console::types::U64::one())));
//
//     bench_speculate_commit_and_finalize(
//         c,
//         "mint_public",
//         || vec![program()],
//         || vec![],
//         || vec![],
//         || vec![("test.aleo", "mint_public", vec![address.clone(), amount.clone()])],
//         NUM_EXECUTIONS,
//     );
//
//     bench_add_next_block(
//         c,
//         "mint_public",
//         || vec![program()],
//         || vec![],
//         || vec![],
//         || vec![("test.aleo", "mint_public", vec![address, amount])],
//         NUM_EXECUTIONS,
//     );
// }
//
// #[cfg(feature = "test-utilities")]
// fn bench_transfer_public(c: &mut Criterion) {
//     let rng = &mut TestRng::default();
//
//     let sender = Value::Plaintext(Plaintext::from(Literal::Address(Address::new(Uniform::rand(rng)))));
//     let recipient = Value::Plaintext(Plaintext::from(Literal::Address(Address::new(Uniform::rand(rng)))));
//     let initial = Value::Plaintext(Plaintext::from(Literal::U64(console::types::U64::new(1_000_000))));
//     let amount = Value::Plaintext(Plaintext::from(Literal::U64(console::types::U64::one())));
//
//     bench_speculate_commit_and_finalize(
//         c,
//         "transfer_public",
//         || vec![program()],
//         || vec![("test.aleo", "mint_public", vec![sender.clone(), initial.clone()])],
//         || vec![],
//         || vec![("test.aleo", "transfer_public", vec![sender.clone(), recipient.clone(), amount.clone()])],
//         NUM_EXECUTIONS,
//     );
//
//     bench_add_next_block(
//         c,
//         "transfer_public",
//         || vec![program()],
//         || vec![("test.aleo", "mint_public", vec![sender.clone(), initial])],
//         || vec![],
//         || vec![("test.aleo", "transfer_public", vec![sender, recipient, amount])],
//         NUM_EXECUTIONS,
//     );
// }
//
// #[cfg(feature = "test-utilities")]
// criterion_group! {
//     name = credits;
//     config = Criterion::default().sample_size(10);
//     targets = bench_mint_public, bench_transfer_public,
// }
// #[cfg(feature = "test-utilities")]
// criterion_main!(credits);
