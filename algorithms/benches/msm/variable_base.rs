// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use snarkvm_algorithms::msm::*;
use snarkvm_curves::{traits::ProjectiveCurve, AffineCurve};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::rand::UniformRand;

use criterion::Criterion;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;

#[macro_use]
extern crate criterion;

fn create_scalar_bases<G: AffineCurve, F: PrimeField>(size: usize) -> (Vec<G>, Vec<F::BigInteger>) {
    let mut rng = XorShiftRng::seed_from_u64(234872845u64);
    let g = (0..size).map(|_| G::rand(&mut rng)).collect::<Vec<_>>();
    let s = (0..size).map(|_| F::rand(&mut rng).to_repr()).collect::<Vec<_>>();
    (g, s)
}

fn variable_base_bls12_377(c: &mut Criterion) {
    use snarkvm_curves::bls12_377::{Fr, G1Affine};

    c.bench_function("MSM Variable Base", move |b| {
        let (bases, scalars) = create_scalar_bases::<G1Affine, Fr>(200000);
        b.iter(|| {
            VariableBaseMSM::multi_scalar_mul(&bases, &scalars);
        })
    });
}

fn variable_base_edwards_bls12(c: &mut Criterion) {
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, Fr};

    c.bench_function("MSM Variable Base", move |b| {
        let (bases, scalars) = create_scalar_bases::<EdwardsAffine, Fr>(200000);
        b.iter(|| {
            VariableBaseMSM::multi_scalar_mul(&bases, &scalars);
        })
    });
}

criterion_group! {
    name = variable_base_group;
    config = Criterion::default().sample_size(10);
    targets = variable_base_bls12_377, variable_base_edwards_bls12
}

criterion_main!(variable_base_group);
