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

use snarkvm_algorithms::{crypto_hash::PoseidonSponge, AlgebraicSponge};
use snarkvm_curves::bls12_377::Fq;
use snarkvm_fields::PoseidonDefaultField;
use snarkvm_utilities::Uniform;

use criterion::Criterion;
use rand::thread_rng;
use std::sync::Arc;

fn sponge_2_1_absorb_4(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let mut sponge = PoseidonSponge::<Fq, 2, 1>::new(&Arc::new(Fq::default_poseidon_parameters::<2>().unwrap()));

    let input = vec![Fq::rand(rng), Fq::rand(rng), Fq::rand(rng), Fq::rand(rng)];
    c.bench_function("PoseidonSponge<2, 1> Absorb 4", move |b| b.iter(|| sponge.absorb(&input)));
}

fn sponge_2_1_absorb_10(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let mut sponge = PoseidonSponge::<Fq, 2, 1>::new(&Arc::new(Fq::default_poseidon_parameters::<2>().unwrap()));

    let input = vec![Fq::rand(rng); 10];
    c.bench_function("PoseidonSponge<2, 1> Absorb 10 ", move |b| b.iter(|| sponge.absorb(&input)));
}

criterion_group! {
    name = sponge;
    config = Criterion::default().sample_size(50);
    targets = sponge_2_1_absorb_4, sponge_2_1_absorb_10
}

criterion_main!(sponge);
