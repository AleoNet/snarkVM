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

use snarkvm_algorithms::msm::*;
use snarkvm_curves::AffineCurve;
use snarkvm_fields::PrimeField;

use criterion::Criterion;
use rand::thread_rng;
use rayon::prelude::*;

#[macro_use]
extern crate criterion;

fn create_scalar_bases<G: AffineCurve<ScalarField = F>, F: PrimeField>(size: usize) -> (Vec<G>, Vec<F::BigInteger>) {
    let bases = (0..size).into_par_iter().map(|_| G::rand(&mut thread_rng())).collect::<Vec<_>>();
    let scalars = (0..size).into_par_iter().map(|_| F::rand(&mut thread_rng()).to_repr()).collect::<Vec<_>>();
    (bases, scalars)
}

fn variable_base_bls12_377(c: &mut Criterion) {
    use snarkvm_curves::bls12_377::{Fr, G1Affine};
    let (bases, scalars) = create_scalar_bases::<G1Affine, Fr>(2000000);

    for size in [10_000, 100_000, 200_000, 300_000, 400_000, 500_000, 1_000_000, 2_000_000] {
        c.bench_function(&format!("VariableBase MSM on BLS12-377 ({})", size), |b| {
            b.iter(|| VariableBase::msm(&bases[..size], &scalars[..size]))
        });
    }
}

fn variable_base_edwards_bls12(c: &mut Criterion) {
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, Fr};
    let (bases, scalars) = create_scalar_bases::<EdwardsAffine, Fr>(1_000_000);

    for size in [10_000, 100_000, 1_000_000] {
        c.bench_function(&format!("Variable MSM on Edwards-BLS12 ({})", size), |b| {
            b.iter(|| VariableBase::msm(&bases[..size], &scalars[..size]))
        });
    }
}

criterion_group! {
    name = variable_base_group;
    config = Criterion::default().sample_size(10);
    targets = variable_base_bls12_377, variable_base_edwards_bls12
}

criterion_main!(variable_base_group);
