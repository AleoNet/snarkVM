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

use snarkvm_algorithms::{
    crypto_hash::PoseidonSponge,
    snark::marlin::{ahp::AHPForR1CS, FiatShamirAlgebraicSpongeRng, MarlinHidingMode, MarlinSNARK},
    SNARK,
};
use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};
use snarkvm_utilities::{ops::MulAssign, Uniform};

use criterion::Criterion;
use rand::{self, thread_rng};

type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, [Fr]>;
type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;

#[derive(Copy, Clone)]
pub struct Benchmark<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_constraints: usize,
    pub num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Benchmark<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.alloc_input(
            || "c",
            || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            },
        )?;

        for i in 0..(self.num_variables - 3) {
            let _ = cs.alloc(|| format!("var {}", i), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for i in 0..(self.num_constraints - 1) {
            cs.enforce(|| format!("constraint {}", i), |lc| lc + a, |lc| lc + b, |lc| lc + c);
        }

        Ok(())
    }
}

fn snark_universal_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000000, 1000000, 1000000).unwrap();

    c.bench_function("snark_universal_setup", move |b| {
        b.iter(|| {
            MarlinInst::universal_setup(&max_degree, rng).unwrap();
        })
    });
}

fn snark_circuit_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

    for size in [100, 1_000, 10_000] {
        let num_constraints = size;
        let num_variables = size;
        let circuit = Benchmark::<Fr> { a: Some(x), b: Some(y), num_constraints, num_variables };
        c.bench_function(&format!("snark_circuit_setup_{size}"), |b| {
            b.iter(|| MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap())
        });
    }
}

fn snark_prove_vk(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

    for size in [100, 1_000, 10_000, 100_000] {
        let num_constraints = size;
        let num_variables = size;
        let circuit = Benchmark::<Fr> { a: Some(x), b: Some(y), num_constraints, num_variables };
        let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

        c.bench_function(&format!("snark_prove_vk_{size}"), move |b| {
            b.iter(|| MarlinInst::prove_vk(&vk, &pk).unwrap())
        });
    }
}

fn snark_verify_vk(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100_000, 100_000, 100_000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

    for size in [100, 1_000, 10_000, 100_000] {
        let num_constraints = size;
        let num_variables = size;
        let circuit = Benchmark::<Fr> { a: Some(x), b: Some(y), num_constraints, num_variables };
        let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        let certificate = MarlinInst::prove_vk(&vk, &pk).unwrap();

        c.bench_function(&format!("snark_verify_vk_{size}"), move |b| {
            b.iter(|| MarlinInst::verify_vk(&circuit, &vk, &certificate).unwrap())
        });
    }
}

fn snark_prove(c: &mut Criterion) {
    let num_constraints = 100;
    let num_variables = 100;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000, 1000, 1000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

    let circuit = Benchmark::<Fr> { a: Some(x), b: Some(y), num_constraints, num_variables };

    let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

    c.bench_function("snark_prove", move |b| b.iter(|| MarlinInst::prove(&params.0, &circuit, rng).unwrap()));
}

fn snark_verify(c: &mut Criterion) {
    let num_constraints = 1000;
    let num_variables = 25;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);
    let mut z = x;
    z.mul_assign(&y);

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000000, 100000, 1000000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

    let circuit = Benchmark::<Fr> { a: Some(x), b: Some(y), num_constraints, num_variables };

    let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

    let proof = MarlinInst::prove(&params.0, &circuit, rng).unwrap();

    c.bench_function("snark_verify", move |b| {
        b.iter(|| {
            let verification = MarlinInst::verify(&params.1, [z], &proof).unwrap();
            assert!(verification);
        })
    });
}

criterion_group! {
    name = marlin_snark;
    config = Criterion::default().sample_size(10);
    targets = snark_universal_setup, snark_circuit_setup, snark_prove_vk, snark_verify_vk, snark_prove, snark_verify,
}

criterion_main!(marlin_snark);
