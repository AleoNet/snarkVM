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

use snarkvm_algorithms::{crh::BHPCRH, traits::CRH};
use snarkvm_curves::edwards_bls12::EdwardsProjective;

use criterion::Criterion;

const SETUP_MESSAGE: &str = "bhp_crh_benchmark";

const INPUT_SIZE: usize = 256;

const BIG_INPUT_SIZE: usize = 18648;

fn setup(c: &mut Criterion) {
    c.bench_function("BHP setup", move |b| {
        b.iter(|| <BHPCRH<EdwardsProjective, INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE))
    });

    c.bench_function("BHP setup (large)", move |b| {
        b.iter(|| <BHPCRH<EdwardsProjective, BIG_INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE))
    });
}

fn hash(c: &mut Criterion) {
    c.bench_function("BHP hash", move |b| {
        let crh = <BHPCRH<EdwardsProjective, INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE);
        let input = (0..INPUT_SIZE).map(|_| rand::random::<bool>()).collect::<Vec<bool>>();

        b.iter(|| crh.hash(&input).unwrap())
    });

    c.bench_function("BHP hash (large)", move |b| {
        let crh = <BHPCRH<EdwardsProjective, BIG_INPUT_SIZE> as CRH>::setup(SETUP_MESSAGE);
        let input = (0..BIG_INPUT_SIZE).map(|_| rand::random::<bool>()).collect::<Vec<bool>>();

        b.iter(|| crh.hash(&input).unwrap())
    });
}

criterion_group! {
    name = bhp_crh;
    config = Criterion::default().sample_size(10);
    targets = setup, hash
}

criterion_main!(bhp_crh);
