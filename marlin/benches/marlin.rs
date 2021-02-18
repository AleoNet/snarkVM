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

use snarkvm_curves::bls12_377::{Bls12_377, Fr};
use snarkvm_errors::gadgets::SynthesisError;
use snarkvm_marlin::snark::MarlinSnark;
use snarkvm_models::{
    algorithms::SNARK,
    curves::Field,
    gadgets::r1cs::{ConstraintSynthesizer, ConstraintSystem},
};

use criterion::Criterion;
use rand::{self, thread_rng, Rng};

type MarlinSNARK = MarlinSnark<'static, Bls12_377, Benchmark<Fr>, Fr>;

#[derive(Clone)]
struct Benchmark<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_variables: usize,
    pub num_constraints: usize,
}

impl<F: Field> ConstraintSynthesizer<F> for Benchmark<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.alloc_input(
            || "c",
            || {
                let a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                Ok(a * &b)
            },
        )?;

        for i in 0..(self.num_variables - 3) {
            let _ = cs.alloc(|| format!("{}", i), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for i in 0..self.num_constraints - 1 {
            cs.enforce(
                || format!("enforce_constraint_{}", i),
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c,
            );
        }

        cs.enforce(|| format!("enforce_final"), |lc| lc, |lc| lc, |lc| lc);

        Ok(())
    }
}

fn snark_setup(c: &mut Criterion) {
    let rng = &mut thread_rng();

    c.bench_function("snark_setup", move |b| {
        b.iter(|| {
            let universal_srs =
                snarkvm_marlin::snark::Marlin::<Bls12_377>::universal_setup(65536, 65536, 65536, rng).unwrap();
            let circuit = Benchmark::<Fr> {
                a: Some(rng.gen()),
                b: Some(rng.gen()),
                num_variables: 10,
                num_constraints: 65536,
            };

            MarlinSNARK::setup(&(circuit, universal_srs), rng).unwrap()
        })
    });
}

fn snark_prove(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let universal_srs = snarkvm_marlin::snark::Marlin::<Bls12_377>::universal_setup(65536, 65536, 65536, rng).unwrap();
    let circuit = Benchmark::<Fr> {
        a: Some(rng.gen()),
        b: Some(rng.gen()),
        num_variables: 10,
        num_constraints: 65536,
    };

    let params = MarlinSNARK::setup(&(circuit.clone(), universal_srs), rng).unwrap();

    c.bench_function("snark_prove", move |b| {
        b.iter(|| MarlinSNARK::prove(&params.0, &circuit, rng).unwrap())
    });
}

criterion_group! {
    name = marlin_snark;
    config = Criterion::default().sample_size(10);
    targets = snark_setup, snark_prove
}

criterion_main!(marlin_snark);
