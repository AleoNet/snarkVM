// Copyright 2024 Aleo Network Foundation
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

use snarkvm_algorithms::{
    AlgebraicSponge,
    SNARK,
    crypto_hash::PoseidonSponge,
    snark::varuna::{CircuitVerifyingKey, TestCircuit, VarunaHidingMode, VarunaSNARK, ahp::AHPForR1CS},
};
use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
use snarkvm_utilities::{CanonicalDeserialize, CanonicalSerialize, TestRng};

use criterion::Criterion;
use std::{collections::BTreeMap, time::Duration};

type VarunaInst = VarunaSNARK<Bls12_377, FS, VarunaHidingMode>;
type FS = PoseidonSponge<Fq, 2, 1>;

fn snark_universal_setup(c: &mut Criterion) {
    let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(1000000, 1000000, 1000000).unwrap();

    c.bench_function("snark_universal_setup", move |b| {
        b.iter(|| {
            VarunaInst::universal_setup(max_degree).unwrap();
        })
    });
}

fn snark_circuit_setup(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();

    for size in [100, 1_000, 10_000] {
        let num_constraints = size;
        let num_variables = size;
        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        c.bench_function(&format!("snark_circuit_setup_{size}"), |b| {
            b.iter(|| VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap())
        });
    }
}

fn snark_prove(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("snark_prove", move |b| {
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;

        let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(1000, 1000, 1000).unwrap();
        let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
        let universal_prover = &universal_srs.to_universal_prover().unwrap();
        let fs_parameters = FS::sample_parameters();

        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let params = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();
        b.iter(|| VarunaInst::prove(universal_prover, &fs_parameters, &params.0, &circuit, rng).unwrap())
    });
}

fn snark_batch_prove(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("snark_batch_prove", move |b| {
        let num_constraints_base = 100;
        let num_variables_base = 25;
        let mul_depth_base = 1;

        let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(1000000, 1000000, 1000000).unwrap();
        let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
        let universal_prover = &universal_srs.to_universal_prover().unwrap();
        let fs_parameters = FS::sample_parameters();

        let circuit_batch_size = 5;
        let instance_batch_size = 5;

        let mut pks = Vec::with_capacity(circuit_batch_size);
        let mut all_circuits = Vec::with_capacity(circuit_batch_size);
        let mut keys_to_constraints = BTreeMap::new();

        for i in 0..circuit_batch_size {
            let num_constraints = num_constraints_base + i;
            let num_variables = num_variables_base + i;
            let mul_depth = mul_depth_base + i;

            let mut circuits = Vec::with_capacity(instance_batch_size);
            for _ in 0..instance_batch_size {
                let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
                circuits.push(circuit);
            }
            let (pk, _) = VarunaInst::circuit_setup(&universal_srs, &circuits[0]).unwrap();
            pks.push(pk);
            all_circuits.push(circuits);
        }

        for i in 0..circuit_batch_size {
            keys_to_constraints.insert(&pks[i], all_circuits[i].as_slice());
        }

        b.iter(|| VarunaInst::prove_batch(universal_prover, &fs_parameters, &keys_to_constraints, rng).unwrap())
    });
}

fn snark_verify(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("snark_verify", move |b| {
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;

        let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100, 100, 100).unwrap();
        let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
        let universal_prover = &universal_srs.to_universal_prover().unwrap();
        let universal_verifier = &universal_srs.to_universal_verifier().unwrap();
        let fs_parameters = FS::sample_parameters();

        let (circuit, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (pk, vk) = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();

        let proof = VarunaInst::prove(universal_prover, &fs_parameters, &pk, &circuit, rng).unwrap();
        b.iter(|| {
            let verification =
                VarunaInst::verify(universal_verifier, &fs_parameters, &vk, public_inputs.as_slice(), &proof).unwrap();
            assert!(verification);
        })
    });
}

fn snark_batch_verify(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    c.bench_function("snark_batch_verify", move |b| {
        let num_constraints_base = 100;
        let num_variables_base = 25;

        let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(1000, 1000, 100).unwrap();
        let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
        let universal_prover = &universal_srs.to_universal_prover().unwrap();
        let universal_verifier = &universal_srs.to_universal_verifier().unwrap();
        let fs_parameters = FS::sample_parameters();

        let circuit_batch_size = 5;
        let instance_batch_size = 5;

        let mut pks = Vec::with_capacity(circuit_batch_size);
        let mut vks = Vec::with_capacity(circuit_batch_size);
        let mut all_circuits = Vec::with_capacity(circuit_batch_size);
        let mut all_inputs = Vec::with_capacity(circuit_batch_size);
        let mut keys_to_constraints = BTreeMap::new();
        let mut keys_to_inputs = BTreeMap::new();
        for i in 0..circuit_batch_size {
            let num_constraints = num_constraints_base + i;
            let num_variables = num_variables_base + i;
            let mul_depth = 1 + i;
            let mut circuits = Vec::with_capacity(circuit_batch_size);
            let mut inputs = Vec::with_capacity(circuit_batch_size);
            for _ in 0..instance_batch_size {
                let (circuit, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
                circuits.push(circuit);
                inputs.push(public_inputs);
            }
            let (pk, vk) = VarunaInst::circuit_setup(&universal_srs, &circuits[0]).unwrap();
            pks.push(pk);
            vks.push(vk);
            all_circuits.push(circuits);
            all_inputs.push(inputs);
        }

        for i in 0..circuit_batch_size {
            keys_to_constraints.insert(&pks[i], all_circuits[i].as_slice());
            keys_to_inputs.insert(&vks[i], all_inputs[i].as_slice());
        }

        let proof = VarunaInst::prove_batch(universal_prover, &fs_parameters, &keys_to_constraints, rng).unwrap();
        b.iter(|| {
            let verification =
                VarunaInst::verify_batch(universal_verifier, &fs_parameters, &keys_to_inputs, &proof).unwrap();
            assert!(verification);
        })
    });
}

fn snark_vk_serialize(c: &mut Criterion) {
    use snarkvm_utilities::serialize::Compress;
    let mut group = c.benchmark_group("snark_vk_serialize");
    let rng = &mut TestRng::default();
    for mode in [Compress::Yes, Compress::No] {
        let name = match mode {
            Compress::No => "uncompressed",
            Compress::Yes => "compressed",
        };
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;

        let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100, 100, 100).unwrap();
        let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (_, vk) = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();
        let mut bytes = Vec::with_capacity(10000);
        group.bench_function(name, |b| {
            b.iter(|| {
                vk.serialize_with_mode(&mut bytes, mode).unwrap();
                bytes.clear()
            })
        });
    }
    group.finish();
}

fn snark_vk_deserialize(c: &mut Criterion) {
    use snarkvm_utilities::serialize::{Compress, Validate};
    let mut group = c.benchmark_group("snark_vk_deserialize");
    let rng = &mut TestRng::default();
    for compress in [Compress::Yes, Compress::No] {
        let compress_name = match compress {
            Compress::No => "uncompressed",
            Compress::Yes => "compressed",
        };
        for validate in [Validate::Yes, Validate::No] {
            let validate_name = match validate {
                Validate::No => "unchecked",
                Validate::Yes => "checked",
            };
            let name = format!("{compress_name}_{validate_name}");
            let num_constraints = 100;
            let num_variables = 25;
            let mul_depth = 1;

            let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100, 100, 100).unwrap();
            let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
            let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

            let (_, vk) = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();
            let mut bytes = Vec::with_capacity(10000);
            vk.serialize_with_mode(&mut bytes, compress).unwrap();
            group.bench_function(name, |b| {
                b.iter(|| {
                    let _vk =
                        CircuitVerifyingKey::<Bls12_377>::deserialize_with_mode(&*bytes, compress, validate).unwrap();
                })
            });
        }
    }
    group.finish();
}

fn snark_certificate_prove(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
    let universal_prover = &universal_srs.to_universal_prover().unwrap();
    let fs_parameters = FS::sample_parameters();
    let fs_p = &fs_parameters;

    for size in [100, 1_000, 10_000, 100_000] {
        let num_constraints = size;
        let num_variables = size;
        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        let (pk, vk) = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();

        c.bench_function(&format!("snark_certificate_prove_{size}"), |b| {
            b.iter(|| VarunaInst::prove_vk(universal_prover, fs_p, &vk, &pk).unwrap())
        });
    }
}

fn snark_certificate_verify(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, VarunaHidingMode>::max_degree(100_000, 100_000, 100_000).unwrap();
    let universal_srs = VarunaInst::universal_setup(max_degree).unwrap();
    let universal_prover = &universal_srs.to_universal_prover().unwrap();
    let universal_verifier = &universal_srs.to_universal_verifier().unwrap();
    let fs_parameters = FS::sample_parameters();
    let fs_p = &fs_parameters;

    for size in [100, 1_000, 10_000, 100_000] {
        let num_constraints = size;
        let num_variables = size;
        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        let (pk, vk) = VarunaInst::circuit_setup(&universal_srs, &circuit).unwrap();
        let certificate = VarunaInst::prove_vk(universal_prover, fs_p, &vk, &pk).unwrap();

        c.bench_function(&format!("snark_certificate_verify_{size}"), |b| {
            b.iter(|| VarunaInst::verify_vk(universal_verifier, fs_p, &circuit, &vk, &certificate).unwrap())
        });
    }
}

criterion_group! {
    name = varuna_snark;
    config = Criterion::default().measurement_time(Duration::from_secs(10));
    targets = snark_universal_setup, snark_circuit_setup, snark_prove, snark_verify, snark_batch_prove, snark_batch_verify, snark_vk_serialize, snark_vk_deserialize, snark_certificate_prove, snark_certificate_verify,
}

criterion_main!(varuna_snark);
