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

#[macro_use]
extern crate criterion;

use snarkvm_curves::{
    bls12_377::{Bls12_377, Fq, Fr},
    bw6_761::BW6_761,
};
use snarkvm_fields::Field;
use snarkvm_gadgets::{curves::bls12_377::PairingGadget as Bls12_377PairingGadget, prelude::*};
use snarkvm_marlin::{
    constraints::{snark::MarlinSNARK, verifier::MarlinVerificationGadget},
    marlin::{MarlinRecursiveMode, MarlinSNARK as MarlinCore},
    FiatShamirAlgebraicSpongeRng,
    PoseidonSponge,
};
use snarkvm_polycommit::sonic_pc::{sonic_kzg10::SonicKZG10Gadget, SonicKZG10};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem, TestConstraintSystem};
use snarkvm_utilities::{ops::MulAssign, UniformRand};

use criterion::Criterion;
use rand::{self, thread_rng};

type MarlinInst = MarlinCore<Fr, Fq, PC, FS, MarlinRecursiveMode>;

type PC = SonicKZG10<Bls12_377>;
type PCGadget = SonicKZG10Gadget<Bls12_377, BW6_761, Bls12_377PairingGadget>;

type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
type TestSNARK = MarlinSNARK<Fr, Fq, PC, FS, MarlinRecursiveMode, Vec<Fr>>;
type TestSNARKGadget = MarlinVerificationGadget<Fr, Fq, PC, PCGadget>;

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
            let _ = cs.alloc(
                || format!("var {}", i),
                || self.a.ok_or(SynthesisError::AssignmentMissing),
            )?;
        }

        for i in 0..(self.num_constraints - 1) {
            cs.enforce(|| format!("constraint {}", i), |lc| lc + a, |lc| lc + b, |lc| lc + c);
        }

        Ok(())
    }
}

fn snark_universal_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(1000000, 1000000, 1000000).unwrap();

    c.bench_function("snark_universal_setup", move |b| {
        b.iter(|| {
            MarlinInst::universal_setup(max_degree, rng).unwrap();
        })
    });
}

fn snark_circuit_setup(c: &mut Criterion) {
    let num_constraints = 100;
    let num_variables = 100;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

    c.bench_function("snark_circuit_setup", move |b| {
        b.iter(|| {
            let circuit = Benchmark::<Fr> {
                a: Some(x),
                b: Some(y),
                num_constraints,
                num_variables,
            };

            MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap()
        })
    });
}

fn snark_prove(c: &mut Criterion) {
    let num_constraints = 100;
    let num_variables = 100;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);

    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(1000, 1000, 1000).unwrap();
    let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        a: Some(x),
        b: Some(y),
        num_constraints,
        num_variables,
    };

    let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

    c.bench_function("snark_prove", move |b| {
        b.iter(|| {
            MarlinInst::prove(
                &params.0,
                &Benchmark {
                    a: Some(x),
                    b: Some(y),
                    num_constraints,
                    num_variables,
                },
                rng,
            )
            .unwrap()
        })
    });
}

fn snark_verify(c: &mut Criterion) {
    let num_constraints = 1000;
    let num_variables = 25;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);
    let mut z = x;
    z.mul_assign(&y);

    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(1000000, 100000, 1000000).unwrap();
    let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        a: Some(x),
        b: Some(y),
        num_constraints,
        num_variables,
    };

    let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

    let proof = MarlinInst::prove(
        &params.0,
        &Benchmark {
            a: Some(x),
            b: Some(y),
            num_constraints,
            num_variables,
        },
        rng,
    )
    .unwrap();

    c.bench_function("snark_verify", move |b| {
        b.iter(|| {
            let verification = MarlinInst::verify(&params.1, &vec![z], &proof).unwrap();
            assert_eq!(verification, true);
        })
    });
}

fn snark_verify_gadget(c: &mut Criterion) {
    let num_constraints = 2000;
    let num_variables = 25;
    let rng = &mut thread_rng();

    let x = Fr::rand(rng);
    let y = Fr::rand(rng);
    let mut z = x;
    z.mul_assign(&y);

    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(1000000, 100000, 1000000).unwrap();
    let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        a: Some(x),
        b: Some(y),
        num_constraints,
        num_variables,
    };

    let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

    let proof = MarlinInst::prove(
        &params.0,
        &Benchmark {
            a: Some(x),
            b: Some(y),
            num_constraints,
            num_variables,
        },
        rng,
    )
    .unwrap();

    let mut cs = TestConstraintSystem::<Fq>::new();

    let input_gadget = <TestSNARKGadget as SNARKVerifierGadget<TestSNARK>>::InputGadget::alloc_input(
        cs.ns(|| "alloc_input_gadget"),
        || Ok(vec![z]),
    )
    .unwrap();

    let proof_gadget =
        <TestSNARKGadget as SNARKVerifierGadget<TestSNARK>>::ProofGadget::alloc(cs.ns(|| "alloc_proof"), || Ok(proof))
            .unwrap();

    let vk_gadget =
        <TestSNARKGadget as SNARKVerifierGadget<TestSNARK>>::VerificationKeyGadget::alloc(cs.ns(|| "alloc_vk"), || {
            Ok(params.1.clone())
        })
        .unwrap();

    c.bench_function("snark_verify_gadget", move |b| {
        b.iter(|| {
            println!("cs: {}", cs.num_constraints());

            <TestSNARKGadget as SNARKVerifierGadget<TestSNARK>>::check_verify(
                cs.ns(|| "marlin_verify"),
                &vk_gadget,
                &input_gadget,
                &proof_gadget,
            )
            .unwrap();

            assert!(
                cs.is_satisfied(),
                "Constraints not satisfied: {}",
                cs.which_is_unsatisfied().unwrap()
            );
        })
    });
}

criterion_group! {
    name = marlin_snark;
    config = Criterion::default().sample_size(10);
    targets = snark_universal_setup, snark_circuit_setup, snark_prove, snark_verify, snark_verify_gadget
}

criterion_main!(marlin_snark);
