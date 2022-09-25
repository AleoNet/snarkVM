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

#[macro_use]
extern crate criterion;

use console::{account::*, network::Testnet3};
use snarkvm_compiler::{CoinbasePuzzle, EpochChallenge, EpochInfo, PuzzleConfig};

use criterion::Criterion;
use rand::{self, thread_rng, CryptoRng, RngCore};

type CoinbasePuzzleInst = CoinbasePuzzle<Testnet3>;

fn sample_inputs(
    degree: usize,
    rng: &mut (impl CryptoRng + RngCore),
) -> (EpochInfo<Testnet3>, EpochChallenge<Testnet3>, Address<Testnet3>, u64) {
    let (epoch_info, epoch_challenge) = sample_epoch_info_and_challenge(degree, rng);
    let (address, nonce) = sample_address_and_nonce(rng);
    (epoch_info, epoch_challenge, address, nonce)
}

fn sample_epoch_info_and_challenge(
    degree: usize,
    rng: &mut (impl CryptoRng + RngCore),
) -> (EpochInfo<Testnet3>, EpochChallenge<Testnet3>) {
    let epoch_info = EpochInfo { epoch_number: rng.next_u64(), previous_block_hash: Default::default() };
    let epoch_challenge = CoinbasePuzzle::init_for_epoch(&epoch_info, degree).unwrap();
    (epoch_info, epoch_challenge)
}

fn sample_address_and_nonce(rng: &mut (impl CryptoRng + RngCore)) -> (Address<Testnet3>, u64) {
    let private_key = PrivateKey::new(rng).unwrap();
    let address = Address::try_from(private_key).unwrap();
    let nonce = rng.next_u64();
    (address, nonce)
}

fn coinbase_puzzle_trim(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 18;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config, rng).unwrap();

    for degree in [1 << 13, 1 << 14, 1 << 15] {
        c.bench_function(&format!("CoinbasePuzzle::Trim 2^{}", (degree as f64).log2()), |b| {
            let config = PuzzleConfig { degree };
            b.iter(|| CoinbasePuzzleInst::trim(&universal_srs, config).unwrap())
        });
    }
}

fn coinbase_puzzle_prove(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 18;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config, rng).unwrap();

    for degree in [1 << 13, 1 << 14, 1 << 15] {
        c.bench_function(&format!("CoinbasePuzzle::Prove 2^{}", (degree as f64).log2()), |b| {
            let config = PuzzleConfig { degree };
            let (pk, _) = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();
            let (epoch_info, epoch_challenge, address, nonce) = sample_inputs(degree, rng);
            b.iter(|| CoinbasePuzzleInst::prove(&pk, &epoch_info, &epoch_challenge, &address, nonce).unwrap())
        });
    }
}

fn coinbase_puzzle_accumulate(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 18;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config, rng).unwrap();

    for degree in [1 << 13, 1 << 14, 1 << 15, 1 << 16] {
        let config = PuzzleConfig { degree };
        let (pk, _) = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();
        let (epoch_info, epoch_challenge) = sample_epoch_info_and_challenge(degree, rng);

        for batch_size in [10, 100, 1000, 10000] {
            c.bench_function(
                &format!("CoinbasePuzzle::Accumulate {batch_size} of 2^{}", (degree as f64).log2()),
                |b| {
                    let solutions = (0..batch_size)
                        .map(|_| {
                            let (address, nonce) = sample_address_and_nonce(rng);
                            CoinbasePuzzleInst::prove(&pk, &epoch_info, &epoch_challenge, &address, nonce).unwrap()
                        })
                        .collect::<Vec<_>>();
                    b.iter(|| CoinbasePuzzleInst::accumulate(&pk, &epoch_info, &epoch_challenge, &solutions).unwrap())
                },
            );
        }
    }
}

fn coinbase_puzzle_verify(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let max_degree = 1 << 18;
    let max_config = PuzzleConfig { degree: max_degree };
    let universal_srs = CoinbasePuzzle::<Testnet3>::setup(max_config, rng).unwrap();

    for degree in [1 << 13, 1 << 14, 1 << 15, 1 << 16] {
        let config = PuzzleConfig { degree };
        let (pk, vk) = CoinbasePuzzleInst::trim(&universal_srs, config).unwrap();
        let (epoch_info, epoch_challenge) = sample_epoch_info_and_challenge(degree, rng);

        for batch_size in [10, 100, 1000, 10000] {
            c.bench_function(&format!("CoinbasePuzzle::Verify {batch_size} of 2^{}", (degree as f64).log2()), |b| {
                let solutions = (0..batch_size)
                    .map(|_| {
                        let (address, nonce) = sample_address_and_nonce(rng);
                        CoinbasePuzzleInst::prove(&pk, &epoch_info, &epoch_challenge, &address, nonce).unwrap()
                    })
                    .collect::<Vec<_>>();
                let final_puzzle =
                    CoinbasePuzzleInst::accumulate(&pk, &epoch_info, &epoch_challenge, &solutions).unwrap();
                b.iter(|| final_puzzle.verify(&vk, &epoch_challenge, &epoch_info).unwrap())
            });
        }
    }
}

criterion_group! {
    name = coinbase_puzzle;
    config = Criterion::default().sample_size(10);
    targets = coinbase_puzzle_trim, coinbase_puzzle_prove, coinbase_puzzle_accumulate, coinbase_puzzle_verify,
}

criterion_main!(coinbase_puzzle);
