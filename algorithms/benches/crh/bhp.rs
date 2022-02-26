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

const NUM_WINDOWS: usize = 8;
const WINDOW_SIZE: usize = 32;

const BIG_NUM_WINDOWS: usize = 296;
const BIG_WINDOW_SIZE: usize = 63;

fn bowe_pedersen_crh_setup(c: &mut Criterion) {
    c.bench_function("BHP CRH setup", move |b| {
        b.iter(|| <BHPCRH<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CRH>::setup("bhp_crh_benchmark"))
    });
}

fn big_bowe_pedersen_crh_setup(c: &mut Criterion) {
    c.bench_function("Big BHP CRH setup", move |b| {
        b.iter(|| <BHPCRH<EdwardsProjective, BIG_NUM_WINDOWS, BIG_WINDOW_SIZE> as CRH>::setup("bhp_crh_benchmark"))
    });
}

fn bowe_pedersen_crh_hash(c: &mut Criterion) {
    let crh = <BHPCRH<EdwardsProjective, NUM_WINDOWS, WINDOW_SIZE> as CRH>::setup("bhp_crh_benchmark");
    let input = vec![127u8; 32];

    c.bench_function("BHP CRH hash", move |b| b.iter(|| crh.hash(&input).unwrap()));
}

fn big_bowe_pedersen_crh_hash(c: &mut Criterion) {
    let crh = <BHPCRH<EdwardsProjective, BIG_NUM_WINDOWS, BIG_WINDOW_SIZE> as CRH>::setup("bhp_crh_benchmark");
    let input = vec![127u8; 32];

    c.bench_function("Big BHP CRH hash", move |b| b.iter(|| crh.hash(&input).unwrap()));
}

criterion_group! {
    name = bowe_crh_setup;
    config = Criterion::default().sample_size(50);
    targets = bowe_pedersen_crh_setup, big_bowe_pedersen_crh_setup
}

criterion_group! {
    name = bowe_crh_hash;
    config = Criterion::default().sample_size(5000);
    targets = bowe_pedersen_crh_hash, big_bowe_pedersen_crh_hash
}

criterion_main!(bowe_crh_setup, bowe_crh_hash);
