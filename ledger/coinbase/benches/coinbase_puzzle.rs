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
    network::{Network, Testnet3},
};
use snarkvm_ledger_coinbase::{CoinbasePuzzle, EpochChallenge, PuzzleConfig};

use criterion::Criterion;
use rand::{self, thread_rng, CryptoRng, RngCore};

type CoinbasePuzzleInst = CoinbasePuzzle<Testnet3>;

fn sample_inputs(
    degree: u32,
    rng: &mut (impl CryptoRng + RngCore),
) -> (EpochChallenge<Testnet3>, Address<Testnet3>, u64) {
    let epoch_challenge = sample_epoch_challenge(degree, rng);
    let (address, nonce) = sample_address_and_nonce(rng);
    (epoch_challenge, address, nonce)
}

fn sample_epoch_challenge(degree: u32, rng: &mut (impl CryptoRng + RngCore)) -> EpochChallenge<Testnet3> {
    EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap()
}

fn sample_address_and_nonce(rng: &mut (impl CryptoRng + RngCore)) -> (Address<Testnet3>, u64) {
    let private_key = PrivateKey::new(rng).unwrap();
    let address = Address::try_from(private_key).unwrap();
    let nonce = rng.next_u64();
    (address, nonce)
}

#[cfg(feature = "setup")]
fn coinbase_puzzle_trim(c: &mut Criterion) {
    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for degree in [(1 << 13) - 1] {
        let config = PuzzleConfig { degree };

        c.bench_function(&format!("CoinbasePuzzle::Trim 2^{}", ((degree + 1) as f64).log2()), |b| {
            b.iter(|| CoinbasePuzzleInst::trim(&universal_srs, config).unwrap())
        });
    }
}

#[cfg(feature = "setup")]
fn coinbase_puzzle_prove(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for degree in [(1 << 13) - 1] {
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();

        c.bench_function(&format!("CoinbasePuzzle::Prove 2^{}", ((degree + 1) as f64).log2()), |b| {
            let (epoch_challenge, address, nonce) = sample_inputs(degree, rng);
            b.iter(|| puzzle.prove(&epoch_challenge, address, nonce, None).unwrap())
        });
    }
}

#[cfg(feature = "setup")]
fn coinbase_puzzle_accumulate(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for degree in [(1 << 13) - 1] {
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();
        let epoch_challenge = sample_epoch_challenge(degree, rng);

        for batch_size in [10, 100, <Testnet3 as Network>::MAX_PROVER_SOLUTIONS] {
            let solutions = (0..batch_size)
                .map(|_| {
                    let (address, nonce) = sample_address_and_nonce(rng);
                    puzzle.prove(&epoch_challenge, address, nonce, None).unwrap()
                })
                .collect::<Vec<_>>();

            c.bench_function(
                &format!("CoinbasePuzzle::Accumulate {batch_size} of 2^{}", ((degree + 1) as f64).log2()),
                |b| b.iter(|| puzzle.accumulate_unchecked(&epoch_challenge, &solutions).unwrap()),
            );
        }
    }
}

#[cfg(feature = "setup")]
fn coinbase_puzzle_verify(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for degree in [(1 << 13) - 1] {
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();
        let epoch_challenge = sample_epoch_challenge(degree, rng);

        for batch_size in [10, 100, <Testnet3 as Network>::MAX_PROVER_SOLUTIONS] {
            let solutions = (0..batch_size)
                .map(|_| {
                    let (address, nonce) = sample_address_and_nonce(rng);
                    puzzle.prove(&epoch_challenge, address, nonce, None).unwrap()
                })
                .collect::<Vec<_>>();
            let solution = puzzle.accumulate_unchecked(&epoch_challenge, &solutions).unwrap();

            c.bench_function(
                &format!("CoinbasePuzzle::Verify {batch_size} of 2^{}", ((degree + 1) as f64).log2()),
                |b| b.iter(|| assert!(puzzle.verify(&solution, &epoch_challenge, 0u64, 0u64).unwrap())),
            );
        }
    }
}

criterion_group! {
    name = coinbase_puzzle;
    config = Criterion::default().sample_size(10);
    targets = coinbase_puzzle_trim, coinbase_puzzle_prove, coinbase_puzzle_accumulate, coinbase_puzzle_verify,
}

criterion_main!(coinbase_puzzle);
