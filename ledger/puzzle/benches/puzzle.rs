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

#![allow(clippy::single_element_loop)]

#[macro_use]
extern crate criterion;

use console::{
    account::*,
    network::{MainnetV0, Network},
};
use snarkvm_ledger_puzzle::{Puzzle, PuzzleSolutions};
use snarkvm_ledger_puzzle_epoch::MerklePuzzle;

use criterion::Criterion;
use rand::{self, thread_rng, CryptoRng, RngCore};

fn sample_address_and_counter(rng: &mut (impl CryptoRng + RngCore)) -> (Address<MainnetV0>, u64) {
    let private_key = PrivateKey::new(rng).unwrap();
    let address = Address::try_from(private_key).unwrap();
    let counter = rng.next_u64();
    (address, counter)
}

fn puzzle_prove(c: &mut Criterion) {
    let rng = &mut thread_rng();

    // Initialize a new puzzle.
    let puzzle = Puzzle::<MainnetV0>::new::<MerklePuzzle<MainnetV0>>();

    // Initialize an epoch hash.
    let epoch_hash = rng.gen();

    c.bench_function("Puzzle::prove", |b| {
        let (address, counter) = sample_address_and_counter(rng);
        b.iter(|| puzzle.prove(epoch_hash, address, counter, None).unwrap())
    });
}

fn puzzle_verify(c: &mut Criterion) {
    let rng = &mut thread_rng();

    // Initialize a new puzzle.
    let puzzle = Puzzle::<MainnetV0>::new::<MerklePuzzle<MainnetV0>>();

    // Initialize an epoch hash.
    let epoch_hash = rng.gen();

    for batch_size in [1, 2, <MainnetV0 as Network>::MAX_SOLUTIONS] {
        let solutions = (0..batch_size)
            .map(|_| {
                let (address, counter) = sample_address_and_counter(rng);
                puzzle.prove(epoch_hash, address, counter, None).unwrap()
            })
            .collect::<Vec<_>>();
        let solutions = PuzzleSolutions::new(solutions).unwrap();

        c.bench_function("Puzzle::check_solutions", |b| {
            b.iter(|| puzzle.check_solutions(&solutions, epoch_hash, 0u64).unwrap())
        });
    }
}

criterion_group! {
    name = puzzle;
    config = Criterion::default().sample_size(10);
    targets = puzzle_prove, puzzle_verify,
}

criterion_main!(puzzle);
