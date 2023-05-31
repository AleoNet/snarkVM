// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{
    snark::marlin::TestCircuit,
    traits::{AlgebraicSponge, SNARK},
};
use std::collections::BTreeMap;

mod marlin {
    use super::*;
    use crate::snark::marlin::{AHPForR1CS, CircuitVerifyingKey, MarlinHidingMode, MarlinNonHidingMode, MarlinSNARK};
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::rand::{TestRng, Uniform};

    type MarlinSonicInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;

    type MarlinSonicPoswInst = MarlinSNARK<Bls12_377, FS, MarlinNonHidingMode>;

    type FS = crate::crypto_hash::PoseidonSponge<Fq, 2, 1>;

    macro_rules! impl_marlin_test {
        ($test_struct: ident, $marlin_inst: tt, $marlin_mode: tt) => {
            struct $test_struct {}
            impl $test_struct {
                pub(crate) fn test_circuit(num_constraints: usize, num_variables: usize) {
                    let rng = &mut snarkvm_utilities::rand::TestRng::default();
                    let random = Fr::rand(rng);

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree).unwrap();
                    let fs_parameters = FS::sample_parameters();

                    for _ in 0..25 {
                        let mul_depth = 2;
                        let (circ, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

                        let (index_pk, index_vk) = $marlin_inst::circuit_setup(&universal_srs, &circ).unwrap();
                        println!("Called circuit setup");

                        let certificate = $marlin_inst::prove_vk(&fs_parameters, &index_vk, &index_pk).unwrap();
                        assert!($marlin_inst::verify_vk(&fs_parameters, &circ, &index_vk, &certificate).unwrap());

                        let proof = $marlin_inst::prove(&fs_parameters, &index_pk, &circ, rng).unwrap();
                        println!("Called prover");

                        assert!($marlin_inst::verify(&fs_parameters, &index_vk, public_inputs, &proof).unwrap());
                        println!("Called verifier");
                        println!("\nShould not verify (i.e. verifier messages should print below):");
                        assert!(!$marlin_inst::verify(&fs_parameters, &index_vk, [random, random], &proof).unwrap());
                    }

                    for circuit_batch_size in (0..5).map(|i| 2usize.pow(i)) {
                        for instance_batch_size in (0..5).map(|i| 2usize.pow(i)) {
                            let mut constraints = BTreeMap::new();
                            let mut inputs = BTreeMap::new();

                            for i in 0..circuit_batch_size {
                                let (circuit_batch, input_batch): (Vec<_>, Vec<_>) = (0..instance_batch_size)
                                .map(|_| {
                                    let mul_depth = 2 + i;
                                    let (circ, inputs) = TestCircuit::gen_rand(mul_depth, num_constraints + 100*i, num_variables, rng);
                                    (circ, inputs)
                                })
                                .unzip();
                                let circuit_id = AHPForR1CS::<Fr, MarlinHidingMode>::index(&circuit_batch[0]).unwrap().id;
                                constraints.insert(circuit_id, circuit_batch);
                                inputs.insert(circuit_id, input_batch);
                            }
                            let unique_instances = constraints.values().map(|instances| &instances[0]).collect::<Vec<_>>();

                            let index_keys =
                                $marlin_inst::batch_circuit_setup(&universal_srs, unique_instances.as_slice()).unwrap();
                            println!("Called circuit setup");

                            let mut pks_to_constraints = BTreeMap::new();
                            let mut vks_to_inputs = BTreeMap::new();
                            let mut constraint_refs = Vec::with_capacity(index_keys.len());
                            for (index_pk, index_vk) in index_keys.iter() {
                                let circuit_constraints = &constraints[&index_pk.circuit.id];
                                let mut circuit_constraint_refs = Vec::with_capacity(circuit_constraints.len());
                                for constraint in circuit_constraints.iter() {
                                    circuit_constraint_refs.push(constraint)
                                }
                                constraint_refs.push(circuit_constraint_refs);
                                let circuit_inputs = &inputs[&index_pk.circuit.id];
                                vks_to_inputs.insert(index_vk, circuit_inputs.as_slice());
                            }
                            for (i, (index_pk, _)) in index_keys.iter().enumerate() {
                                pks_to_constraints.insert(index_pk, constraint_refs[i].as_slice());
                            }

                            let proof =
                                $marlin_inst::prove_batch(&fs_parameters, &pks_to_constraints, rng).unwrap();
                            println!("Called prover");

                            assert!(
                                $marlin_inst::verify_batch(&fs_parameters, &vks_to_inputs, &proof).unwrap(),
                                "Batch verification failed with {instance_batch_size} instances and {circuit_batch_size} circuits for circuits: {constraints:?}"
                            );
                            println!("Called verifier");
                            println!("\nShould not verify (i.e. verifier messages should print below):");
                            let mut fake_instance_inputs = Vec::with_capacity(vks_to_inputs.len());
                            for instance_input in vks_to_inputs.values() {
                                let mut fake_instance_input = Vec::with_capacity(instance_input.len());
                                for input in instance_input.iter() {
                                    let fake_input = vec![Fr::rand(rng); input.len()];
                                    fake_instance_input.push(fake_input);
                                }
                                fake_instance_inputs.push(fake_instance_input);
                            }
                            let mut vks_to_fake_inputs = BTreeMap::new();
                            for (i, vk) in vks_to_inputs.keys().enumerate() {
                                vks_to_fake_inputs.insert(*vk, fake_instance_inputs[i].as_slice());
                            }
                            assert!(
                                !$marlin_inst::verify_batch(
                                    &fs_parameters,
                                    &vks_to_fake_inputs,
                                    &proof
                                )
                                .unwrap()
                            );
                        }
                    }
                }

                pub(crate) fn test_serde_json(num_constraints: usize, num_variables: usize) {
                    use std::str::FromStr;

                    let rng = &mut TestRng::default();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree).unwrap();

                    let mul_depth = 1;
                    let (circ, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

                    let (_index_pk, index_vk) = $marlin_inst::circuit_setup(&universal_srs, &circ).unwrap();
                    println!("Called circuit setup");

                    // Serialize
                    let expected_string = index_vk.to_string();
                    let candidate_string = serde_json::to_string(&index_vk).unwrap();
                    assert_eq!(
                        expected_string,
                        serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap()
                    );

                    // Deserialize
                    assert_eq!(index_vk, CircuitVerifyingKey::from_str(&expected_string).unwrap());
                    assert_eq!(index_vk, serde_json::from_str(&candidate_string).unwrap());
                }

                pub(crate) fn test_bincode(num_constraints: usize, num_variables: usize) {
                    use snarkvm_utilities::{FromBytes, ToBytes};

                    let rng = &mut TestRng::default();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree).unwrap();

                    let mul_depth = 1;
                    let (circ, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

                    let (_index_pk, index_vk) = $marlin_inst::circuit_setup(&universal_srs, &circ).unwrap();
                    println!("Called circuit setup");

                    // Serialize
                    let expected_bytes = index_vk.to_bytes_le().unwrap();
                    let candidate_bytes = bincode::serialize(&index_vk).unwrap();
                    // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
                    assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

                    // Deserialize
                    assert_eq!(index_vk, CircuitVerifyingKey::read_le(&expected_bytes[..]).unwrap());
                    assert_eq!(index_vk, bincode::deserialize(&candidate_bytes[..]).unwrap());
                }
            }
        };
    }

    impl_marlin_test!(SonicPCTest, MarlinSonicInst, MarlinHidingMode);
    impl_marlin_test!(SonicPCPoswTest, MarlinSonicPoswInst, MarlinNonHidingMode);

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        SonicPCTest::test_circuit(num_constraints, num_variables);
        SonicPCPoswTest::test_circuit(num_constraints, num_variables);

        SonicPCTest::test_serde_json(num_constraints, num_variables);
        SonicPCPoswTest::test_serde_json(num_constraints, num_variables);

        SonicPCTest::test_bincode(num_constraints, num_variables);
        SonicPCPoswTest::test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        SonicPCTest::test_circuit(num_constraints, num_variables);
        SonicPCPoswTest::test_circuit(num_constraints, num_variables);

        SonicPCTest::test_serde_json(num_constraints, num_variables);
        SonicPCPoswTest::test_serde_json(num_constraints, num_variables);

        SonicPCTest::test_bincode(num_constraints, num_variables);
        SonicPCPoswTest::test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        SonicPCTest::test_circuit(num_constraints, num_variables);
        SonicPCPoswTest::test_circuit(num_constraints, num_variables);

        SonicPCTest::test_serde_json(num_constraints, num_variables);
        SonicPCPoswTest::test_serde_json(num_constraints, num_variables);

        SonicPCTest::test_bincode(num_constraints, num_variables);
        SonicPCPoswTest::test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        SonicPCTest::test_circuit(num_constraints, num_variables);
        SonicPCPoswTest::test_circuit(num_constraints, num_variables);

        SonicPCTest::test_serde_json(num_constraints, num_variables);
        SonicPCPoswTest::test_serde_json(num_constraints, num_variables);

        SonicPCTest::test_bincode(num_constraints, num_variables);
        SonicPCPoswTest::test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        SonicPCTest::test_circuit(num_constraints, num_variables);
        SonicPCPoswTest::test_circuit(num_constraints, num_variables);

        SonicPCTest::test_serde_json(num_constraints, num_variables);
        SonicPCPoswTest::test_serde_json(num_constraints, num_variables);

        SonicPCTest::test_bincode(num_constraints, num_variables);
        SonicPCPoswTest::test_bincode(num_constraints, num_variables);
    }
}

mod marlin_hiding {
    use super::*;
    use crate::{
        crypto_hash::PoseidonSponge,
        snark::marlin::{ahp::AHPForR1CS, CircuitVerifyingKey, MarlinHidingMode, MarlinSNARK},
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::{
        rand::{TestRng, Uniform},
        FromBytes,
        ToBytes,
    };

    use std::str::FromStr;

    type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;
    type FS = PoseidonSponge<Fq, 2, 1>;

    fn test_circuit_n_times(num_constraints: usize, num_variables: usize, num_times: usize) {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        for _ in 0..num_times {
            let mul_depth = 2;
            let (circuit, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

            let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
            println!("Called circuit setup");

            let proof = MarlinInst::prove(&fs_parameters, &index_pk, &circuit, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&fs_parameters, &index_vk, public_inputs, &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&fs_parameters, &index_vk, [Fr::rand(rng), Fr::rand(rng)], &proof).unwrap());
        }
    }

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        test_circuit_n_times(num_constraints, num_variables, 100)
    }

    fn test_serde_json(num_constraints: usize, num_variables: usize) {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();

        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (_index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        println!("Called circuit setup");

        // Serialize
        let expected_string = index_vk.to_string();
        let candidate_string = serde_json::to_string(&index_vk).unwrap();
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());

        // Deserialize
        assert_eq!(index_vk, CircuitVerifyingKey::from_str(&expected_string).unwrap());
        assert_eq!(index_vk, serde_json::from_str(&candidate_string).unwrap());
    }

    fn test_bincode(num_constraints: usize, num_variables: usize) {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();

        let mul_depth = 1;
        let (circuit, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let (_index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        println!("Called circuit setup");

        // Serialize
        let expected_bytes = index_vk.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&index_vk).unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(index_vk, CircuitVerifyingKey::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(index_vk, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
        test_serde_json(num_constraints, num_variables);
        test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
        test_serde_json(num_constraints, num_variables);
        test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit(num_constraints, num_variables);
        test_serde_json(num_constraints, num_variables);
        test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit(num_constraints, num_variables);
        test_serde_json(num_constraints, num_variables);
        test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
        test_serde_json(num_constraints, num_variables);
        test_bincode(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_large_matrix() {
        let num_constraints = 1 << 16;
        let num_variables = 1 << 16;

        test_circuit_n_times(num_constraints, num_variables, 1);
    }

    #[test]
    fn check_indexing() {
        let rng = &mut TestRng::default();
        let mul_depth = 2;
        let num_constraints = 1 << 13;
        let num_variables = 1 << 13;
        let (circuit, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        println!("Called circuit setup");

        let proof = MarlinInst::prove(&fs_parameters, &index_pk, &circuit, rng).unwrap();
        println!("Called prover");

        universal_srs.download_powers_for(0..2usize.pow(18)).unwrap();
        let (new_pk, new_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
        assert_eq!(index_pk, new_pk);
        assert_eq!(index_vk, new_vk);
        assert!(MarlinInst::verify(&fs_parameters, &index_vk, public_inputs.clone(), &proof).unwrap());
        assert!(MarlinInst::verify(&fs_parameters, &new_vk, public_inputs, &proof).unwrap());
    }

    #[test]
    fn test_srs_downloads() {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        // Indexing, proving, and verifying for a circuit with 1 << 13 constraints and 1 << 13 variables.
        let mul_depth = 2;
        let num_constraints = 2usize.pow(15) - 10;
        let num_variables = 2usize.pow(15) - 10;
        let (circuit1, public_inputs1) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        let (pk1, vk1) = MarlinInst::circuit_setup(&universal_srs, &circuit1).unwrap();
        println!("Called circuit setup");

        let proof1 = MarlinInst::prove(&fs_parameters, &pk1, &circuit1, rng).unwrap();
        println!("Called prover");
        assert!(MarlinInst::verify(&fs_parameters, &vk1, public_inputs1.clone(), &proof1).unwrap());

        /*****************************************************************************/

        // Indexing, proving, and verifying for a circuit with 1 << 19 constraints and 1 << 19 variables.
        let mul_depth = 2;
        let num_constraints = 2usize.pow(19) - 10;
        let num_variables = 2usize.pow(19) - 10;
        let (circuit2, public_inputs2) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        let (pk2, vk2) = MarlinInst::circuit_setup(&universal_srs, &circuit2).unwrap();
        println!("Called circuit setup");

        let proof2 = MarlinInst::prove(&fs_parameters, &pk2, &circuit2, rng).unwrap();
        println!("Called prover");
        assert!(MarlinInst::verify(&fs_parameters, &vk2, public_inputs2, &proof2).unwrap());
        /*****************************************************************************/
        assert!(MarlinInst::verify(&fs_parameters, &vk1, public_inputs1, &proof1).unwrap());
    }
}
