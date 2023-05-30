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

#[macro_use]
extern crate criterion;

use snarkvm_algorithms::{crypto_hash::PoseidonSponge, AlgebraicSponge};
use snarkvm_curves::bls12_377::Fq;
use snarkvm_utilities::{TestRng, Uniform};

use criterion::Criterion;

fn sponge_2_1_absorb_4(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let mut sponge = PoseidonSponge::<Fq, 2, 1>::new();

    let input = vec![Fq::rand(rng), Fq::rand(rng), Fq::rand(rng), Fq::rand(rng)];
    c.bench_function("PoseidonSponge<2, 1> Absorb 4", move |b| b.iter(|| sponge.absorb_native_field_elements(&input)));
}

fn sponge_2_1_absorb_10(c: &mut Criterion) {
    let rng = &mut TestRng::default();
    let mut sponge = PoseidonSponge::<Fq, 2, 1>::new();

    let input = vec![Fq::rand(rng); 10];
    c.bench_function("PoseidonSponge<2, 1> Absorb 10 ", move |b| {
        b.iter(|| sponge.absorb_native_field_elements(&input))
    });
}

criterion_group! {
    name = sponge;
    config = Criterion::default().sample_size(50);
    targets = sponge_2_1_absorb_4, sponge_2_1_absorb_10
}

criterion_main!(sponge);
