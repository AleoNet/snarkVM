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

pub(crate) mod g1 {
    use snarkvm_curves::{
        bls12_377::{Fr, G1Affine, G1Projective as G1},
        traits::ProjectiveCurve,
        AffineCurve,
    };
    use snarkvm_utilities::rand::Uniform;

    use criterion::Criterion;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::{AddAssign, MulAssign};

    pub fn bench_g1_rand(c: &mut Criterion) {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
        c.bench_function("bls12_377: g1_rand", |c| c.iter(|| G1::rand(&mut rng)));
    }

    pub fn bench_g1_mul_assign(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G1, Fr)> = (0..SAMPLES).map(|_| (G1::rand(&mut rng), Fr::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g1_mul_assign", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.mul_assign(v[count].1);
                count = (count + 1) % SAMPLES;
            })
        });
    }

    pub fn bench_g1_add_assign(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G1, G1)> = (0..SAMPLES).map(|_| (G1::rand(&mut rng), G1::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g1_add_assign", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.add_assign(v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g1_add_assign_mixed(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G1, G1Affine)> = (0..SAMPLES).map(|_| (G1::rand(&mut rng), G1::rand(&mut rng).into())).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g1_add_assign_mixed", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.add_assign_mixed(&v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g1_double(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G1, G1)> = (0..SAMPLES).map(|_| (G1::rand(&mut rng), G1::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g1_double", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.double_in_place();
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g1_check_subgroup_membership(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<G1> = (0..SAMPLES).map(|_| G1::rand(&mut rng)).collect();
        let v = G1::batch_normalization_into_affine(v);

        let mut count = 0;
        c.bench_function("bls12_377: g1_is_in_correct_subgroup", |c| {
            c.iter(|| {
                let result = v[count].is_in_correct_subgroup_assuming_on_curve();
                count = (count + 1) % SAMPLES;
                result
            })
        });
    }
}

pub(crate) mod g2 {
    use snarkvm_curves::{
        bls12_377::{Fr, G2Affine, G2Projective as G2},
        traits::ProjectiveCurve,
    };
    use snarkvm_utilities::rand::Uniform;

    use criterion::Criterion;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::{AddAssign, MulAssign};

    pub fn bench_g2_rand(c: &mut Criterion) {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);
        c.bench_function("bls12_377: g2_rand", |c| c.iter(|| G2::rand(&mut rng)));
    }

    pub fn bench_g2_mul_assign(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G2, Fr)> = (0..SAMPLES).map(|_| (G2::rand(&mut rng), Fr::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g2_mul_assign", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.mul_assign(v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g2_add_assign(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G2, G2)> = (0..SAMPLES).map(|_| (G2::rand(&mut rng), G2::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g2_add_assign", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.add_assign(v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g2_add_assign_mixed(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G2, G2Affine)> = (0..SAMPLES).map(|_| (G2::rand(&mut rng), G2::rand(&mut rng).into())).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g2_add_assign_mixed", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.add_assign_mixed(&v[count].1);
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }

    pub fn bench_g2_double(c: &mut Criterion) {
        const SAMPLES: usize = 1000;

        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        let v: Vec<(G2, G2)> = (0..SAMPLES).map(|_| (G2::rand(&mut rng), G2::rand(&mut rng))).collect();

        let mut count = 0;
        c.bench_function("bls12_377: g2_double", |c| {
            c.iter(|| {
                let mut tmp = v[count].0;
                tmp.double_in_place();
                count = (count + 1) % SAMPLES;
                tmp
            })
        });
    }
}
