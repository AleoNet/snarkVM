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

use snarkvm_algorithms::{crh::PedersenCRH, traits::CRH};
use snarkvm_curves::edwards_bls12::EdwardsProjective;

use criterion::Criterion;

const SETUP_MESSAGE: &str = "pedersen_crh_benchmark";

const INPUT_SIZE: usize = 256;

const BIG_INPUT_SIZE: usize = 18648;

fn setup(c: &mut Criterion) {
    c.bench_function("Pedersen setup", move |b| {
        b.iter(|| <PedersenCRH<EdwardsProjective, INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE))
    });

    c.bench_function("Pedersen setup (large)", move |b| {
        b.iter(|| <PedersenCRH<EdwardsProjective, BIG_INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE))
    });
}

fn hash(c: &mut Criterion) {
    c.bench_function("Pedersen hash", move |b| {
        let crh = <PedersenCRH<EdwardsProjective, INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE);
        let input = (0..INPUT_SIZE).map(|_| rand::random::<bool>()).collect::<Vec<bool>>();

        b.iter(|| crh.hash(&input).unwrap())
    });

    c.bench_function("Pedersen hash (large)", move |b| {
        let crh = <PedersenCRH<EdwardsProjective, BIG_INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE);
        let input = (0..BIG_INPUT_SIZE).map(|_| rand::random::<bool>()).collect::<Vec<bool>>();

        b.iter(|| crh.hash(&input).unwrap())
    });
}

criterion_group! {
    name = pedersen_crh;
    config = Criterion::default().sample_size(10);
    targets = setup, hash
}

criterion_main!(pedersen_crh);
