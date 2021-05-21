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

use snarkvm_algorithms::traits::SNARK;
use snarkvm_curves::{
    bls12_377::{Bls12_377, Fq, Fr},
    bw6_761::BW6_761,
};
use snarkvm_fields::Field;
use snarkvm_gadgets::curves::bls12_377::PairingGadget as Bls12_377PairingGadget;
use snarkvm_marlin::{
    constraints::snark::MarlinSNARKGadget,
    marlin::{MarlinRecursiveMode, MarlinSNARK},
    snark::MarlinSystem,
    FiatShamirAlgebraicSpongeRng,
    FiatShamirAlgebraicSpongeRngVar,
    PoseidonSponge,
    PoseidonSpongeVar,
};
use snarkvm_polycommit::marlin_pc::{marlin_kzg10::MarlinKZG10Gadget, MarlinKZG10};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

use criterion::Criterion;
use rand::{self, thread_rng, Rng};

type Marlin = MarlinSystem<Bls12_377, Benchmark<Fr>, Vec<Fr>>;

type PC = MarlinKZG10<Bls12_377>;
type PCGadget = MarlinKZG10Gadget<Bls12_377, BW6_761, Bls12_377PairingGadget>;

type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>;
type FSG = FiatShamirAlgebraicSpongeRngVar<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>;

type MarlinCore = MarlinSNARK<Fr, Fq, PC, FS, MarlinRecursiveMode>;

type TestSNARKGadget = MarlinSNARKGadget<Fr, Fq, PC, FS, MarlinRecursiveMode, PCGadget, FSG>;

struct Benchmark<F: Field> {
    inputs: Vec<Option<F>>,
    num_constraints: usize,
}

impl<F: Field> ConstraintSynthesizer<F> for Benchmark<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        assert!(self.inputs.len() >= 2);
        assert!(self.num_constraints >= self.inputs.len());

        let mut variables: Vec<_> = Vec::with_capacity(self.inputs.len());
        for (i, input) in self.inputs.iter().cloned().enumerate() {
            let input_var = cs.alloc_input(
                || format!("input_{}", i),
                || input.ok_or(SynthesisError::AssignmentMissing),
            )?;
            variables.push((input, input_var));
        }

        for i in 0..self.num_constraints {
            let new_entry = {
                let (input_1_val, input_1_var) = variables[i];
                let (input_2_val, input_2_var) = variables[i + 1];
                let result_val = input_1_val.and_then(|input_1| input_2_val.map(|input_2| input_1 * &input_2));
                let result_var = cs.alloc(
                    || format!("result_{}", i),
                    || result_val.ok_or(SynthesisError::AssignmentMissing),
                )?;
                cs.enforce(
                    || format!("enforce_constraint_{}", i),
                    |lc| lc + input_1_var,
                    |lc| lc + input_2_var,
                    |lc| lc + result_var,
                );
                (result_val, result_var)
            };
            variables.push(new_entry);
        }
        Ok(())
    }
}

fn snark_universal_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("snark_universal_setup", move |b| {
        b.iter(|| {
            MarlinCore::universal_setup(1000000, 1000000, 1000000, rng).unwrap();
        })
    });
}

fn snark_circuit_setup(c: &mut Criterion) {
    let num_inputs = 2;
    let num_constraints = 10000;
    let rng = &mut thread_rng();
    let mut inputs: Vec<Option<Fr>> = Vec::with_capacity(num_inputs);
    for _ in 0..num_inputs {
        inputs.push(Some(rng.gen()));
    }

    let universal_srs = MarlinCore::universal_setup(100000, 100000, 100000, rng).unwrap();

    c.bench_function("snark_circuit_setup", move |b| {
        b.iter(|| {
            let circuit = Benchmark::<Fr> {
                inputs: vec![None; num_inputs],
                num_constraints,
            };

            Marlin::setup(&(circuit, universal_srs.clone()), rng).unwrap()
        })
    });
}

fn snark_prove(c: &mut Criterion) {
    let num_inputs = 2;
    let num_constraints = 1000;
    let rng = &mut thread_rng();
    let mut inputs: Vec<Option<Fr>> = Vec::with_capacity(num_inputs);
    for _ in 0..num_inputs {
        inputs.push(Some(rng.gen()));
    }

    let universal_srs = MarlinCore::universal_setup(1000, 1000, 1000, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        inputs: vec![None; num_inputs],
        num_constraints,
    };

    let params = Marlin::setup(&(circuit, universal_srs), rng).unwrap();

    c.bench_function("snark_prove", move |b| {
        b.iter(|| {
            Marlin::prove(
                &params.0,
                &Benchmark {
                    inputs: inputs.clone(),
                    num_constraints,
                },
                rng,
            )
            .unwrap()
        })
    });
}

fn snark_verify(c: &mut Criterion) {
    let num_inputs = 2;
    let num_constraints = 1000;
    let rng = &mut thread_rng();
    let mut inputs: Vec<Option<Fr>> = Vec::with_capacity(num_inputs);
    for _ in 0..num_inputs {
        inputs.push(Some(rng.gen()));
    }

    let universal_srs = snarkvm_marlin::MarlinTestnet1::universal_setup(1000, 1000, 1000, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        inputs: vec![None; num_inputs],
        num_constraints,
    };

    let params = Marlin::setup(&(circuit, universal_srs), rng).unwrap();

    let proof = Marlin::prove(
        &params.0,
        &Benchmark {
            inputs: inputs.clone(),
            num_constraints,
        },
        rng,
    )
    .unwrap();

    let public_inputs: Vec<_> = inputs.iter().map(|x| x.unwrap()).collect();

    c.bench_function("snark_prove", move |b| {
        b.iter(|| {
            let verification = Marlin::verify(&params.1, &public_inputs, &proof).unwrap();
            assert_eq!(verification, true);
        })
    });
}

fn snark_verify_gadget(c: &mut Criterion) {
    let num_inputs = 2;
    let num_constraints = 1000;
    let rng = &mut thread_rng();
    let mut inputs: Vec<Option<Fr>> = Vec::with_capacity(num_inputs);
    for _ in 0..num_inputs {
        inputs.push(Some(rng.gen()));
    }

    let universal_srs = snarkvm_marlin::MarlinTestnet1::universal_setup(1000, 1000, 1000, rng).unwrap();

    let circuit = Benchmark::<Fr> {
        inputs: vec![None; num_inputs],
        num_constraints,
    };

    let params = Marlin::setup(&(circuit, universal_srs), rng).unwrap();

    let proof = Marlin::prove(
        &params.0,
        &Benchmark {
            inputs: inputs.clone(),
            num_constraints,
        },
        rng,
    )
    .unwrap();

    let public_inputs: Vec<_> = inputs.iter().map(|x| x.unwrap()).collect();

    c.bench_function("snark_prove", move |b| {
        b.iter(|| {
            let verification = Marlin::verify(&params.1, &public_inputs, &proof).unwrap();
            assert_eq!(verification, true);
        })
    });
}

criterion_group! {
    name = marlin_snark;
    config = Criterion::default().sample_size(10);
    targets = snark_universal_setup, snark_circuit_setup, snark_prove, snark_verify
}

criterion_main!(marlin_snark);
