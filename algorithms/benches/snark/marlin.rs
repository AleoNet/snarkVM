// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    snark::marlin::{ahp::AHPForR1CS, CircuitVerifyingKey, MarlinHidingMode, MarlinSNARK, TestCircuit},
    AlgebraicSponge,
    SNARK,
};
use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
use snarkvm_utilities::{CanonicalDeserialize, CanonicalSerialize, TestRng};

use criterion::Criterion;

use itertools::Itertools;
use std::collections::BTreeMap;

type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;
type FS = PoseidonSponge<Fq, 2, 1>;

fn snark_universal_setup(c: &mut Criterion) {
    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000000, 1000000, 1000000).unwrap();

    c.bench_function("snark_universal_setup", move |b| {
        b.iter(|| {
            MarlinInst::universal_setup(&max_degree).unwrap();
        })
    });
}

fn snark_circuit_setup(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();

    for size in [100, 1_000, 10_000] {
        let num_constraints = size;
        let num_variables = size;
        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        c.bench_function(&format!("snark_circuit_setup_{size}"), |b| {
            b.iter(|| MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap())
        });
    }
}

fn snark_prove(c: &mut Criterion) {
    c.bench_function("snark_prove", move |b| {
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000, 1000, 1000).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let params = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        b.iter(|| MarlinInst::prove(&fs_parameters, &params.0, &circuit, rng).unwrap())
    });
}

fn snark_batch_prove(c: &mut Criterion) {
    c.bench_function("snark_batch_prove", move |b| {
        let num_constraints_base = 100;
        let num_variables_base = 25;
        let mul_depth_base = 1;
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000000, 1000000, 1000000).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
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
            let (pk, _) = MarlinInst::circuit_setup(&universal_srs, &circuits[0]).unwrap();
            pks.push(pk);
            all_circuits.push(circuits);
        }
        // We need to create references to the circuits we just created
        let all_circuit_refs = (0..circuit_batch_size)
            .map(|i| (0..instance_batch_size).map(|j| &all_circuits[i][j]).collect_vec())
            .collect_vec();

        for i in 0..circuit_batch_size {
            keys_to_constraints.insert(&pks[i], all_circuit_refs[i].as_slice());
        }
        b.iter(|| MarlinInst::prove_batch(&fs_parameters, &keys_to_constraints, rng).unwrap())
    });
}

fn snark_verify(c: &mut Criterion) {
    c.bench_function("snark_verify", move |b| {
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 100, 100).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        let (circuit, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

        let proof = MarlinInst::prove(&fs_parameters, &pk, &circuit, rng).unwrap();
        b.iter(|| {
            let verification = MarlinInst::verify(&fs_parameters, &vk, public_inputs.as_slice(), &proof).unwrap();
            assert!(verification);
        })
    });
}

fn snark_batch_verify(c: &mut Criterion) {
    c.bench_function("snark_batch_verify", move |b| {
        let num_constraints_base = 100;
        let num_variables_base = 25;
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(1000, 1000, 100).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
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
            let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuits[0]).unwrap();
            pks.push(pk);
            vks.push(vk);
            all_circuits.push(circuits);
            all_inputs.push(inputs);
        }
        // We need to create references to the circuits and inputs we just created
        let all_circuit_refs = (0..circuit_batch_size)
            .map(|i| (0..instance_batch_size).map(|j| &all_circuits[i][j]).collect_vec())
            .collect_vec();

        for i in 0..circuit_batch_size {
            keys_to_constraints.insert(&pks[i], all_circuit_refs[i].as_slice());
            keys_to_inputs.insert(&vks[i], all_inputs[i].as_slice());
        }

        let proof = MarlinInst::prove_batch(&fs_parameters, &keys_to_constraints, rng).unwrap();
        b.iter(|| {
            let verification = MarlinInst::verify_batch(&fs_parameters, &keys_to_inputs, &proof).unwrap();
            assert!(verification);
        })
    });
}

fn snark_vk_serialize(c: &mut Criterion) {
    use snarkvm_utilities::serialize::Compress;
    let mut group = c.benchmark_group("snark_vk_serialize");
    for mode in [Compress::Yes, Compress::No] {
        let name = match mode {
            Compress::No => "uncompressed",
            Compress::Yes => "compressed",
        };
        let num_constraints = 100;
        let num_variables = 25;
        let mul_depth = 1;
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 100, 100).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (_, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
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
            let rng = &mut TestRng::default();

            let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 100, 100).unwrap();
            let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
            let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

            let (_, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
            let mut bytes = Vec::with_capacity(10000);
            vk.serialize_with_mode(&mut bytes, compress).unwrap();
            group.bench_function(name, |b| {
                b.iter(|| {
                    let _vk = CircuitVerifyingKey::<Bls12_377, MarlinHidingMode>::deserialize_with_mode(
                        &*bytes, compress, validate,
                    )
                    .unwrap();
                })
            });
        }
    }
    group.finish();
}

fn snark_certificate_prove(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100000, 100000, 100000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
    let fs_parameters = FS::sample_parameters();
    let fs_p = &fs_parameters;

    for size in [100, 1_000, 10_000, 100_000] {
        c.bench_function(&format!("snark_certificate_prove_{size}"), |b| {
            let num_constraints = size;
            let num_variables = size;
            let mul_depth = 1;
            let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
            let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();

            b.iter(|| MarlinInst::prove_vk(fs_p, &vk, &pk).unwrap())
        });
    }
}

fn snark_certificate_verify(c: &mut Criterion) {
    let rng = &mut TestRng::default();

    let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100_000, 100_000, 100_000).unwrap();
    let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
    let fs_parameters = FS::sample_parameters();
    let fs_p = &fs_parameters;

    for size in [100, 1_000, 10_000, 100_000] {
        c.bench_function(&format!("snark_certificate_verify_{size}"), |b| {
            let num_constraints = size;
            let num_variables = size;
            let mul_depth = 1;
            let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
            let (pk, vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
            let certificate = MarlinInst::prove_vk(fs_p, &vk, &pk).unwrap();

            b.iter(|| MarlinInst::verify_vk(fs_p, &circuit, &vk, &certificate).unwrap())
        });
    }
}

criterion_group! {
    name = marlin_snark;
    config = Criterion::default().sample_size(10);
    targets = snark_universal_setup, snark_circuit_setup, snark_prove, snark_verify, snark_batch_prove, snark_batch_verify, snark_vk_serialize, snark_vk_deserialize, snark_certificate_prove, snark_certificate_verify,
}

criterion_main!(marlin_snark);
