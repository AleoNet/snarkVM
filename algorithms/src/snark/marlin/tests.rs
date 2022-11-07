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

use crate::traits::{AlgebraicSponge, SNARK};
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

#[derive(Copy, Clone)]
pub struct Circuit<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_constraints: usize,
    pub num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
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
        let d = cs.alloc_input(
            || "d",
            || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
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
        cs.enforce(|| "constraint_final", |lc| lc + c, |lc| lc + b, |lc| lc + d);

        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::snark::marlin::{AHPForR1CS, CircuitVerifyingKey, MarlinHidingMode, MarlinNonHidingMode, MarlinSNARK};
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::rand::{TestRng, Uniform};

    use core::ops::MulAssign;

    type MarlinSonicInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;

    type MarlinSonicPoswInst = MarlinSNARK<Bls12_377, FS, MarlinNonHidingMode>;

    type FS = crate::crypto_hash::PoseidonSponge<Fq, 2, 1>;

    macro_rules! impl_marlin_test {
        ($test_struct: ident, $marlin_inst: tt, $marlin_mode: tt) => {
            struct $test_struct {}
            impl $test_struct {
                pub(crate) fn test_circuit(num_constraints: usize, num_variables: usize) {
                    let rng = &mut snarkvm_utilities::rand::TestRng::default();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree).unwrap();
                    let fs_parameters = FS::sample_parameters();

                    for _ in 0..50 {
                        let a = Fr::rand(rng);
                        let b = Fr::rand(rng);
                        let mut c = a;
                        c.mul_assign(&b);
                        let mut d = c;
                        d.mul_assign(&b);

                        let circ = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };

                        let (index_pk, index_vk) = $marlin_inst::circuit_setup(&universal_srs, &circ).unwrap();
                        println!("Called circuit setup");

                        let certificate = $marlin_inst::prove_vk(&fs_parameters, &index_vk, &index_pk).unwrap();
                        assert!($marlin_inst::verify_vk(&fs_parameters, &circ, &index_vk, &certificate).unwrap());

                        let proof = $marlin_inst::prove(&fs_parameters, &index_pk, &circ, rng).unwrap();
                        println!("Called prover");

                        assert!($marlin_inst::verify(&fs_parameters, &index_vk, [c, d], &proof).unwrap());
                        println!("Called verifier");
                        println!("\nShould not verify (i.e. verifier messages should print below):");
                        assert!(!$marlin_inst::verify(&fs_parameters, &index_vk, [a, a], &proof).unwrap());
                    }

                    for _ in 0..10 {
                        for batch_size in (0..5).map(|i| 2usize.pow(i)) {
                            let (circuit_batch, input_batch): (Vec<_>, Vec<_>) = (0..batch_size)
                                .map(|_| {
                                    let a = Fr::rand(rng);
                                    let b = Fr::rand(rng);
                                    let mut c = a;
                                    c.mul_assign(&b);
                                    let mut d = c;
                                    d.mul_assign(&b);

                                    let circ = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };
                                    (circ, [c, d])
                                })
                                .unzip();
                            let (index_pk, index_vk) =
                                $marlin_inst::circuit_setup(&universal_srs, &circuit_batch[0]).unwrap();
                            println!("Called circuit setup");

                            let proof =
                                $marlin_inst::prove_batch(&fs_parameters, &index_pk, &circuit_batch, rng).unwrap();
                            println!("Called prover");

                            assert!(
                                $marlin_inst::verify_batch(&fs_parameters, &index_vk, &input_batch, &proof).unwrap(),
                                "Batch verification failed with {batch_size} inputs"
                            );
                            println!("Called verifier");
                            println!("\nShould not verify (i.e. verifier messages should print below):");
                            assert!(
                                !$marlin_inst::verify_batch(
                                    &fs_parameters,
                                    &index_vk,
                                    &vec![[Fr::rand(rng), Fr::rand(rng)]; batch_size],
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

                    let circ =
                        Circuit { a: Some(Fr::rand(rng)), b: Some(Fr::rand(rng)), num_constraints, num_variables };

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

                    let circ =
                        Circuit { a: Some(Fr::rand(rng)), b: Some(Fr::rand(rng)), num_constraints, num_variables };

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

    use core::ops::MulAssign;
    use std::str::FromStr;

    type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;
    type FS = PoseidonSponge<Fq, 2, 1>;

    fn test_circuit_n_times(num_constraints: usize, num_variables: usize, num_times: usize) {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        for _ in 0..num_times {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circuit = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };

            let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
            println!("Called circuit setup");

            let proof = MarlinInst::prove(&fs_parameters, &index_pk, &circuit, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&fs_parameters, &index_vk, [c, d], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&fs_parameters, &index_vk, [a, a], &proof).unwrap());
        }
    }

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        test_circuit_n_times(num_constraints, num_variables, 100)
    }

    fn test_serde_json(num_constraints: usize, num_variables: usize) {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();

        let circuit = Circuit { a: Some(Fr::rand(rng)), b: Some(Fr::rand(rng)), num_constraints, num_variables };

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

        let circuit = Circuit { a: Some(Fr::rand(rng)), b: Some(Fr::rand(rng)), num_constraints, num_variables };

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

    fn setup_test(num_constraints: usize, num_variables: usize) -> (Circuit<Fr>, Fr, Fr) {
        let rng = &mut TestRng::default();
        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = a * b;
        let d = c * b;

        (Circuit { a: Some(a), b: Some(b), num_constraints, num_variables }, c, d)
    }

    #[test]
    fn check_indexing() {
        let rng = &mut TestRng::default();
        let (circuit, c, d) = setup_test(1 << 13, 1 << 13);

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
        assert!(MarlinInst::verify(&fs_parameters, &index_vk, [c, d], &proof).unwrap());
        assert!(MarlinInst::verify(&fs_parameters, &new_vk, [c, d], &proof).unwrap());
    }

    #[test]
    fn test_srs_downloads() {
        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_parameters = FS::sample_parameters();

        // Indexing, proving, and verifying for a circuit with 1 << 13 constraints and 1 << 13 variables.
        let (circuit1, c1, d1) = setup_test(2usize.pow(15) - 10, 2usize.pow(15) - 10);
        let (pk1, vk1) = MarlinInst::circuit_setup(&universal_srs, &circuit1).unwrap();
        println!("Called circuit setup");

        let proof1 = MarlinInst::prove(&fs_parameters, &pk1, &circuit1, rng).unwrap();
        println!("Called prover");
        assert!(MarlinInst::verify(&fs_parameters, &vk1, [c1, d1], &proof1).unwrap());

        /*****************************************************************************/

        // Indexing, proving, and verifying for a circuit with 1 << 19 constraints and 1 << 19 variables.
        let (circuit2, c2, d2) = setup_test(2usize.pow(19) - 10, 2usize.pow(19) - 10);
        let (pk2, vk2) = MarlinInst::circuit_setup(&universal_srs, &circuit2).unwrap();
        println!("Called circuit setup");

        let proof2 = MarlinInst::prove(&fs_parameters, &pk2, &circuit2, rng).unwrap();
        println!("Called prover");
        assert!(MarlinInst::verify(&fs_parameters, &vk2, [c2, d2], &proof2).unwrap());
        /*****************************************************************************/
        assert!(MarlinInst::verify(&fs_parameters, &vk1, [c1, d1], &proof1).unwrap());
    }
}
