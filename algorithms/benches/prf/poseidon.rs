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

use snarkvm_algorithms::{prf::PoseidonPRF, traits::PRF};
use snarkvm_curves::bls12_377::Fr;
use snarkvm_utilities::Uniform;

use criterion::Criterion;
use rand::thread_rng;

fn poseidon_prf(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("PoseidonPRF PRF evaluation", move |b| {
        let input: Vec<_> = vec![Uniform::rand(rng)];
        let seed = Uniform::rand(rng);

        b.iter(|| PoseidonPRF::<Fr, 4>::prf(&seed, &input))
    });
}

criterion_group! {
    name = prf;
    config = Criterion::default().sample_size(50);
    targets = poseidon_prf
}

criterion_main!(prf);
