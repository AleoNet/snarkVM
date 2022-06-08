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

use snarkvm_algorithms::{commitment::bhp::BHPCommitment, traits::CommitmentScheme};
use snarkvm_curves::edwards_bls12::EdwardsProjective;
use snarkvm_utilities::rand::Uniform;

use criterion::Criterion;
use rand::{
    thread_rng,
    {self},
};

const NUM_WINDOWS: usize = 16;
const WINDOW_SIZE: usize = 32;

fn bhp_commitment_setup(c: &mut Criterion) {
    c.bench_function("BHP Commitment Setup", move |b| {
        b.iter(|| {
            <BHPCommitment<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CommitmentScheme>::setup(
                "bhp_commitment_benchmark",
            )
        })
    });
}

fn bhp_commitment_evaluation(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let parameters = <BHPCommitment<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CommitmentScheme>::setup(
        "bhp_commitment_benchmark",
    );
    let input = vec![127u8; 256];

    c.bench_function("BHP Commitment Evaluation", move |b| {
        b.iter(|| {
            let randomness =
                <BHPCommitment<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CommitmentScheme>::Randomness::rand(rng);
            <BHPCommitment<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CommitmentScheme>::commit_bytes(
                &parameters,
                &input,
                &randomness,
            )
            .unwrap()
        })
    });
}

criterion_group! {
    name = commitment_setup;
    config = Criterion::default().sample_size(50);
    targets = bhp_commitment_setup
}

criterion_group! {
    name = commitment_evaluation;
    config = Criterion::default().sample_size(50);
    targets = bhp_commitment_evaluation
}

criterion_main!(commitment_setup, commitment_evaluation);
