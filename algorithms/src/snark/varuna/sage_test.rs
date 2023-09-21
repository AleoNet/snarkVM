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

#[cfg(test)]
mod tests {
    use crate::{
        snark::varuna::{ahp::verifier, TestCircuit, VarunaNonHidingMode, VarunaSNARK},
        traits::snark::SNARK,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_fields::One;
    use std::ops::Deref;
    type FS = crate::crypto_hash::PoseidonSponge<Fq, 2, 1>;
    type MM = VarunaNonHidingMode;
    type VarunaSonicInst = VarunaSNARK<Bls12_377, FS, MM>;
    use crate::snark::varuna::AHPForR1CS;
    use std::{fmt::Debug, fs, str::FromStr};

    use crate::fft::EvaluationDomain;
    use std::{collections::BTreeMap, path::PathBuf, sync::Arc};

    /// Returns the path to the `resources` folder for this module.
    fn resources_path() -> PathBuf {
        // Construct the path for the `resources` folder.
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("src");
        path.push("snark");
        path.push("varuna");
        path.push("resources");

        // Create the `resources` folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir_all(&path).unwrap_or_else(|_| panic!("Failed to create resources folder: {path:?}"));
        }
        // Output the path.
        path
    }

    /// Loads the given `test_folder/test_file` and asserts the given `candidate` matches the expected values.
    #[track_caller]
    fn assert_snapshot<S1: Into<String>, S2: Into<String>, C: Debug>(test_folder: S1, test_file: S2, candidate: C) {
        // Construct the path for the test folder.
        let mut path = resources_path();
        path.push(test_folder.into());

        // Create the test folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir(&path).unwrap_or_else(|_| panic!("Failed to create test folder: {path:?}"));
        }

        // Construct the path for the test file.
        path.push(test_file.into());
        path.set_extension("test_vector");

        // Create the test file, if it does not exist.
        if !path.exists() {
            std::fs::File::create(&path).unwrap_or_else(|_| panic!("Failed to create file: {path:?}"));
        }

        // Assert the test file is equal to the expected value.
        expect_test::expect_file![path].assert_eq(&format!("{candidate:?}"));
    }

    // TODO: make macros to use different hiding modes
    #[test]
    fn test_prover_sage_vectors() {
        let input_path = "src/snark/varuna/resources/inputs.txt";
        let test_vectors_file = fs::read_to_string(input_path).expect("Could not read the file");
        let mut test_vectors = Vec::new(); // TODO: preallocate
        for line in test_vectors_file.lines() {
            test_vectors.push(line.to_string())
        }

        let instance_path = "src/snark/varuna/resources/instance.input";
        let instance_file = fs::read_to_string(instance_path).expect("Could not read the file");
        let mut instance = Vec::new(); // TODO: preallocate
        for line in instance_file.lines() {
            instance.push(line.to_string())
        }

        let challenges_path = "src/snark/varuna/resources/challenges.input";
        let challenges_file = fs::read_to_string(challenges_path).expect("Could not read the file");
        let mut challenges = Vec::new(); // TODO: preallocate
        for line in challenges_file.lines() {
            challenges.push(line.to_string())
        }
        let circuit_combiner = Fr::one();
        let instance_combiners = vec![Fr::one()];

        use snarkvm_curves::bls12_377::FrParameters;
        use snarkvm_fields::Fp256;
        let mut random_state = vec![0u64; 100];
        let add_f_to_state = |s: &mut Vec<u64>, f: Fp256<FrParameters>| {
            // Fp384 field elements sample 6 u64 values in total
            for i in 0..f.0.0.len() {
                s.push(f.0.0[f.0.0.len() - 1 - i]);
            }
        };
        for witness in instance[15].split(",") {
            println!("witness: {}", witness.trim());
            if witness.trim() == "" {
                continue;
            }
            add_f_to_state(&mut random_state, Fr::from_str(witness.trim()).unwrap());
        }
        // let two = Fq::from_str("2").unwrap();
        // add_f_to_state(&mut random_state, 2u64);
        // random_state.push(79601084644714804u64);
        // random_state.push(11090443381845330384u64);
        // random_state.push(17770411857874044427u64);
        // random_state.push(4538334656037814244u64);
        // random_state.push(11709709805437321058u64);
        // random_state.push(404198066556501712u64);

        let rng = &mut snarkvm_utilities::rand::TestMockRng::fixed(random_state);

        // let test = Fq::from_str("8").unwrap();
        // println!("test: {:?}", test.0.0);

        // let a = Fq::rand(rng);
        // println!("a: {:?}", a);
        // println!("a: {:?}", a.0.0[0]);
        // println!("a: {:?}", a.0.0[1]);
        // println!("a: {:?}", a.0.0[2]);
        // println!("a: {:?}", a.0.0[3]);
        // println!("a: {:?}", a.0.0[4]);
        // println!("a: {:?}", a.0.0[5]);
        // let a = Fq::rand(rng);
        // println!("a: {:?}", a);

        let max_degree = AHPForR1CS::<Fr, MM>::max_degree(100, 25, 300).unwrap();
        let universal_srs = VarunaSonicInst::universal_setup(max_degree).unwrap();
        let mul_depth = 3;
        let num_constraints = 7;
        let num_variables = 7;
        // TODO: pass the right randomness in
        let (circ, public_inputs) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        println!("public_inputs: {:?}", public_inputs);
        println!("circ: {:?}", circ);
        let (index_pk, _index_vk) = VarunaSonicInst::circuit_setup(&universal_srs, &circ).unwrap();
        let mut keys_to_constraints = BTreeMap::new();
        keys_to_constraints.insert(index_pk.circuit.deref(), std::slice::from_ref(&circ));

        let prover_state = AHPForR1CS::<_, MM>::init_prover(&keys_to_constraints, rng).unwrap();
        let prover_state = AHPForR1CS::<_, MM>::prover_first_round(prover_state, rng).unwrap();
        let first_round_oracles = Arc::clone(prover_state.first_round_oracles.as_ref().unwrap());
        println!("first_round_oracles: {:?}", first_round_oracles);

        let assignments = AHPForR1CS::<_, MM>::calculate_assignments(&prover_state).unwrap();
        let constraint_domain = EvaluationDomain::<Fr>::new(num_constraints).unwrap();
        println!("assignments: {:?}", assignments);
        println!("generator of H: {:?}", constraint_domain.group_gen);
        for el in constraint_domain.elements() {
            println!("element of H: {:?}", el);
        }
        let non_zero_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_a).unwrap();
        println!("generator of K: {:?}", non_zero_domain.group_gen);
        for el in non_zero_domain.elements() {
            println!("element of K: {:?}", el);
        }

        let combiners = verifier::BatchCombiners::<Fr> { circuit_combiner, instance_combiners };
        let batch_combiners = BTreeMap::from_iter([(index_pk.circuit.id, combiners)]);
        let verifier_first_msg = verifier::FirstMessage::<Fr> { batch_combiners };
        println!("verifier_first_msg: {:?}", verifier_first_msg);

        let (second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_msg, prover_state).unwrap();
        println!("second_oracles: {:?}", second_oracles);

        // TODO: hardcoding for testing purposes
        let alpha = Fr::from_str("22").unwrap();
        let eta_b = Fr::from_str("22").unwrap();
        let eta_c = Fr::from_str("22").unwrap();
        let beta = Fr::from_str("22").unwrap();
        let delta_a = vec![Fr::from_str("22").unwrap()];
        let delta_b = vec![Fr::from_str("22").unwrap()];
        let delta_c = vec![Fr::from_str("22").unwrap()];
        let gamma = Fr::from_str("22").unwrap();
        let verifier_second_msg = verifier::SecondMessage::<Fr> { alpha, eta_b, eta_c };
        let (prover_third_message, third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_first_msg, &verifier_second_msg, prover_state, rng)
                .unwrap();

        println!("\n");
        println!("prover_third_message\n:{:?}", prover_third_message);
        println!("\n");
        println!("third_oracles g1 polynomial\n:{:?}", third_oracles.g_1);
        println!("\n");
        println!("third_oracles h1 polynomial\n:{:?}", third_oracles.h_1);
        println!("\n");

        let verifier_third_msg = verifier::ThirdMessage::<Fr> { beta };

        println!("verifier_third_msg\n:{:?}", verifier_third_msg);
        println!("\n");

        let (prover_fourth_message, fourth_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_fourth_round(&verifier_second_msg, &verifier_third_msg, prover_state, rng)
                .unwrap();

        println!("prover_fourth_message: {:?}", prover_fourth_message);
        println!("\n");
        println!("fourth_oracles\n:{:?}", fourth_oracles);
        println!("\n");

        let verifier_fourth_msg = verifier::FourthMessage::<Fr> { delta_a, delta_b, delta_c };
        println!("verifier_fourth_msg\n:{:?}", verifier_fourth_msg);
        println!("\n");

        let mut public_inputs = BTreeMap::new();
        let public_input = prover_state.public_inputs(&index_pk.circuit).unwrap();
        public_inputs.insert(index_pk.circuit.id, public_input);
        let non_zero_a_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_a).unwrap();
        let non_zero_b_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_b).unwrap();
        let non_zero_c_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_c).unwrap();
        let variable_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_variables).unwrap();
        let constraint_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_constraints).unwrap();
        let input_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_public_inputs).unwrap();

        let fifth_oracles =
            AHPForR1CS::<_, MM>::prover_fifth_round(verifier_fourth_msg.clone(), prover_state, rng).unwrap();

        println!("fifth_oracles\n:{:?}", fifth_oracles);
        println!("\n");
        println!("fifth_oracles h_2polynomial\n:{:?}", fifth_oracles.h_2);

        use std::marker::PhantomData;
        let mut circuit_specific_states = BTreeMap::new();
        let circuit_specific_state = verifier::CircuitSpecificState {
            input_domain,
            variable_domain,
            constraint_domain,
            non_zero_a_domain,
            non_zero_b_domain,
            non_zero_c_domain,
            batch_size: 1,
        };
        circuit_specific_states.insert(index_pk.circuit.id, circuit_specific_state);
        let verifier_state = verifier::State {
            circuit_specific_states,
            max_constraint_domain: constraint_domain,
            max_variable_domain: variable_domain,
            max_non_zero_domain: non_zero_domain, // TODO: currently assuming same for three matrices but we should take the max
            first_round_message: Some(verifier_first_msg),
            second_round_message: Some(verifier_second_msg),
            third_round_message: Some(verifier_third_msg),
            fourth_round_message: Some(verifier_fourth_msg),
            gamma: Some(gamma),
            mode: PhantomData,
        };
        println!("verifier_state: {:?}", verifier_state);

        let polynomials: Vec<_> = index_pk
            .circuit
            .iter()
            .chain(first_round_oracles.iter())
            .chain(second_oracles.iter())
            .chain(third_oracles.iter())
            .chain(fourth_oracles.iter())
            .chain(fifth_oracles.iter())
            .collect();

        println!("polynomials: {:?}", polynomials);
        println!("\n");

        let _lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &polynomials,
            &prover_third_message,
            &prover_fourth_message,
            &verifier_state,
        )
        .unwrap();

        println!("lc_s: {:?}", _lc_s);
        println!("\n");

        // TODO: I can save space by using bytes instead of number characters, and allocating the right amount immediately
        let mut h_0 = String::new();
        for coeff in second_oracles.h_0.coeffs() {
            h_0 += &coeff.1.to_string();
            h_0 += ",";
        }
        assert_snapshot("test_rounds", "h_0", h_0);

        // TODO: check all oracles
    }
}
