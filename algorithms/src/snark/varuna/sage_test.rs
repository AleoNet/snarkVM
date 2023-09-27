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
        fft::EvaluationDomain,
        snark::varuna::{ahp::verifier, AHPForR1CS, TestCircuit, VarunaNonHidingMode, VarunaSNARK},
        traits::snark::SNARK,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr, FrParameters};
    use snarkvm_fields::{Fp256, One};
    use std::{collections::BTreeMap, fs, ops::Deref, path::PathBuf, str::FromStr, sync::Arc};

    type FS = crate::crypto_hash::PoseidonSponge<Fq, 2, 1>;
    type MM = VarunaNonHidingMode;
    type VarunaSonicInst = VarunaSNARK<Bls12_377, FS, MM>;

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
    fn assert_snapshot<S1: Into<String>, S2: Into<String>>(test_folder: S1, test_file: S2, candidate: &str) {
        // Construct the path for the test folder.
        let mut path = resources_path();
        path.push(test_folder.into());

        // Create the test folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir(&path).unwrap_or_else(|_| panic!("Failed to create test folder: {path:?}"));
        }

        // Construct the path for the test file.
        path.push(test_file.into());
        path.set_extension("txt");

        // Create the test file, if it does not exist.
        if !path.exists() {
            panic!("Test file does not exist: {path:?}");
        }

        println!("Testing path: {:?}", path);

        // Assert the test file is equal to the expected value.
        expect_test::expect_file![path].assert_eq(candidate);
    }

    fn create_test_vector(folder: &str, file: &str, data: &str) {
        // Construct the path for the test folder.
        let mut path = resources_path();
        path.push(folder);

        // Create the test folder, if it does not exist.
        if !path.exists() {
            std::fs::create_dir(&path).unwrap_or_else(|_| panic!("Failed to create test folder: {path:?}"));
        }

        // Construct the path for the test file.
        path.push(file);
        path.set_extension("txt");

        // Create the test file, if it does not exist.
        if !path.exists() {
            std::fs::File::create(&path).unwrap_or_else(|_| panic!("Failed to create file: {path:?}"));
        }

        std::fs::write(&path, data).unwrap_or_else(|_| panic!("Failed to write to file: {:?}", path));
    }

    #[test]
    fn test_proving_system_with_test_vectors() {
        run_prover_sage_vectors(false);
    }

    #[test]
    #[ignore]
    fn create_prover_test_vectors() {
        run_prover_sage_vectors(true);
    }

    // TODO: make macros to use different hiding modes
    fn run_prover_sage_vectors(create_test_vectors: bool) {
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

        let mut random_state = vec![0u64; 100];
        let add_f_to_state = |s: &mut Vec<u64>, f: Fp256<FrParameters>| {
            // Fp384 field elements sample 6 u64 values in total.
            for i in 0..f.0.0.len() {
                s.push(f.0.0[f.0.0.len() - 1 - i]);
            }
        };
        for witness in instance[15].split(',') {
            if witness.trim() == "" {
                continue;
            }
            add_f_to_state(&mut random_state, Fr::from_str(witness.trim()).unwrap());
        }

        let rng = &mut snarkvm_utilities::rand::TestMockRng::fixed(random_state);

        let max_degree = AHPForR1CS::<Fr, MM>::max_degree(100, 25, 300).unwrap();
        let universal_srs = VarunaSonicInst::universal_setup(max_degree).unwrap();
        let mul_depth = 3;
        let num_constraints = 7;
        let num_variables = 7;

        // TODO: pass the right randomness in
        let (circ, _) = TestCircuit::gen_rand(mul_depth, num_constraints, num_variables, rng);
        let (index_pk, _index_vk) = VarunaSonicInst::circuit_setup(&universal_srs, &circ).unwrap();
        let mut keys_to_constraints = BTreeMap::new();
        keys_to_constraints.insert(index_pk.circuit.deref(), std::slice::from_ref(&circ));

        let prover_state = AHPForR1CS::<_, MM>::init_prover(&keys_to_constraints, rng).unwrap();
        let prover_state = AHPForR1CS::<_, MM>::prover_first_round(prover_state, rng).unwrap();
        let first_round_oracles = Arc::clone(prover_state.first_round_oracles.as_ref().unwrap());

        // Get private witness polynomial coefficients.
        // TODO: Support batched circuits
        let (_, w_poly) = first_round_oracles.batches.iter().next().unwrap();
        let w_lde = format!("{:?}", w_poly[0].0.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "w_lde", &w_lde);
        }

        // Generate test vectors from assignments.
        let assignments = AHPForR1CS::<_, MM>::calculate_assignments(&prover_state).unwrap();

        // Get full witness polynomial coefficients.
        // TODO: Support batched circuits
        let (_, z_poly) = assignments.iter().next().unwrap();
        let z_lde = format!("{:?}", z_poly[0].coeffs().iter().collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "z_lde", &z_lde);
        }

        let combiners = verifier::BatchCombiners::<Fr> { circuit_combiner, instance_combiners };
        let batch_combiners = BTreeMap::from_iter([(index_pk.circuit.id, combiners)]);
        let verifier_first_msg = verifier::FirstMessage::<Fr> { batch_combiners };

        let (second_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_second_round(&verifier_first_msg, prover_state).unwrap();

        // Get round 2 rowcheck polynomial oracle coefficients.
        let h_0 = format!("{:?}", second_oracles.h_0.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "h_0", &h_0);
        }

        // TODO: hardcoding for testing purposes
        let alpha =
            Fr::from_str("3848747268438146429751199396409351181775389242768022193485885831738448017147").unwrap();
        let eta_b =
            Fr::from_str("8197944265508088395536605774074305135172727109973647025295290482999689956740").unwrap();
        let eta_c =
            Fr::from_str("969057258436037177120044092706484307847087860293738150232755543560372962965").unwrap();
        let beta =
            Fr::from_str("1261454636320080423466301508402274008580035865105120100172548996301504688503").unwrap();
        let delta_a = vec![Fr::from_str("1").unwrap()];
        let delta_b =
            vec![Fr::from_str("4987583518937978349829618221849930643691403053432331091973338029344238378359").unwrap()];
        let delta_c =
            vec![Fr::from_str("5292820491592383411924896857610185298390500160570506754003580089093852949536").unwrap()];
        let gamma =
            Fr::from_str("672738024541753390172108082983901395072703770443783662610485842877496432861").unwrap();
        let verifier_second_msg = verifier::SecondMessage::<Fr> { alpha, eta_b, eta_c };
        let (prover_third_message, third_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_third_round(&verifier_first_msg, &verifier_second_msg, prover_state, rng)
                .unwrap();

        // Get coefficients round 3 univariate rowcheck polynomial oracles.
        let g_1 = format!("{:?}", third_oracles.g_1.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "g_1", &g_1);
        }
        let h_1 = format!("{:?}", third_oracles.h_1.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "h_1", &h_1);
        }

        let verifier_third_msg = verifier::ThirdMessage::<Fr> { beta };
        let (prover_fourth_message, fourth_oracles, prover_state) =
            AHPForR1CS::<_, MM>::prover_fourth_round(&verifier_second_msg, &verifier_third_msg, prover_state, rng)
                .unwrap();

        // Create round 4 rational sumcheck oracle polynomials.
        // TODO: Provide support for batched circuits
        let (_, gm_polys) = fourth_oracles.gs.iter().next().unwrap();
        let g_a = format!("{:?}", gm_polys.g_a.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        let g_b = format!("{:?}", gm_polys.g_b.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        let g_c = format!("{:?}", gm_polys.g_b.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "g_a", &g_a);
            create_test_vector("polynomials", "g_b", &g_b);
            create_test_vector("polynomials", "g_c", &g_c);
        }

        // Create the verifier's fourth message.
        let verifier_fourth_msg = verifier::FourthMessage::<Fr> { delta_a, delta_b, delta_c };

        let mut public_inputs = BTreeMap::new();
        let public_input = prover_state.public_inputs(&index_pk.circuit).unwrap();
        public_inputs.insert(index_pk.circuit.id, public_input);
        let non_zero_a_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_a).unwrap();
        let non_zero_b_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_b).unwrap();
        let non_zero_c_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_non_zero_c).unwrap();
        let variable_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_variables).unwrap();
        let constraint_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_constraints).unwrap();
        let input_domain = EvaluationDomain::<Fr>::new(index_pk.circuit.index_info.num_public_inputs).unwrap();

        // Get constraint domain elements.
        let mut constraint_domain_elements = Vec::with_capacity(constraint_domain.size());
        for el in constraint_domain.elements() {
            constraint_domain_elements.push(el);
        }
        if create_test_vectors {
            create_test_vector("domain", "R", &format!("{:?}", constraint_domain_elements));
        }

        // Get non_zero_domain elements.
        let non_zero_domain = *[&non_zero_a_domain, &non_zero_b_domain, &non_zero_c_domain]
            .iter()
            .max_by_key(|domain| domain.size)
            .unwrap();
        let mut non_zero_domain_elements = Vec::with_capacity(non_zero_domain.size());
        for el in non_zero_domain.elements() {
            non_zero_domain_elements.push(el);
        }
        if create_test_vectors {
            create_test_vector("domain", "K", &format!("{:?}", constraint_domain_elements));
        }

        // Get variable domain elements.
        let mut variable_domain_elements = Vec::with_capacity(input_domain.size());
        for el in variable_domain.elements() {
            variable_domain_elements.push(el);
        }
        if create_test_vectors {
            create_test_vector("domain", "C", &format!("{:?}", constraint_domain_elements));
        }

        let fifth_oracles =
            AHPForR1CS::<_, MM>::prover_fifth_round(verifier_fourth_msg.clone(), prover_state, rng).unwrap();

        // Get coefficients of final oracle polynomial from round 5.
        let h_2 = format!("{:?}", fifth_oracles.h_2.coeffs().map(|(_, coeff)| coeff).collect::<Vec<_>>());
        if create_test_vectors {
            create_test_vector("polynomials", "h_2", &h_2);
        }

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
            max_non_zero_domain: *non_zero_domain,
            first_round_message: Some(verifier_first_msg),
            second_round_message: Some(verifier_second_msg),
            third_round_message: Some(verifier_third_msg),
            fourth_round_message: Some(verifier_fourth_msg),
            gamma: Some(gamma),
            mode: std::marker::PhantomData,
        };

        let polynomials: Vec<_> = index_pk
            .circuit
            .iter()
            .chain(first_round_oracles.iter())
            .chain(second_oracles.iter())
            .chain(third_oracles.iter())
            .chain(fourth_oracles.iter())
            .chain(fifth_oracles.iter())
            .collect();

        let _lc_s = AHPForR1CS::<_, MM>::construct_linear_combinations(
            &public_inputs,
            &polynomials,
            &prover_third_message,
            &prover_fourth_message,
            &verifier_state,
        )
        .unwrap();

        // Check the intermediate oracle polynomials against the test vectors.
        assert_snapshot("polynomials", "w_lde", &w_lde);
        assert_snapshot("polynomials", "z_lde", &z_lde);
        assert_snapshot("polynomials", "h_0", &h_0);
        assert_snapshot("polynomials", "h_1", &h_1);
        assert_snapshot("polynomials", "g_1", &g_1);
        assert_snapshot("polynomials", "h_2", &h_2);
        assert_snapshot("polynomials", "g_a", &g_a);
        assert_snapshot("polynomials", "g_b", &g_b);
        assert_snapshot("polynomials", "g_c", &g_c);

        // Check that the domains match the test vectors.
        assert_snapshot("domain", "R", &format!("{:?}", constraint_domain_elements));
        assert_snapshot("domain", "K", &format!("{:?}", non_zero_domain_elements));
        assert_snapshot("domain", "C", &format!("{:?}", variable_domain_elements));
    }
}
