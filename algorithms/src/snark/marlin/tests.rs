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

use crate::traits::SNARK;
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
    use crate::snark::marlin::{
        fiat_shamir::FiatShamirChaChaRng,
        AHPForR1CS,
        CircuitVerifyingKey,
        MarlinHidingMode,
        MarlinNonHidingMode,
        MarlinSNARK,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::rand::{test_crypto_rng, Uniform};

    use blake2::Blake2s256;
    use core::ops::MulAssign;

    type MarlinSonicInst = MarlinSNARK<Bls12_377, FiatShamirChaChaRng<Fr, Fq, Blake2s256>, MarlinHidingMode, [Fr]>;

    type MarlinSonicPoswInst =
        MarlinSNARK<Bls12_377, FiatShamirChaChaRng<Fr, Fq, Blake2s256>, MarlinNonHidingMode, [Fr]>;

    macro_rules! impl_marlin_test {
        ($test_struct: ident, $marlin_inst: tt, $marlin_mode: tt) => {
            struct $test_struct {}
            impl $test_struct {
                pub(crate) fn test_circuit(num_constraints: usize, num_variables: usize) {
                    let rng = &mut snarkvm_utilities::rand::test_crypto_rng();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree, rng).unwrap();

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

                        let proof = $marlin_inst::prove(&index_pk, &circ, rng).unwrap();
                        println!("Called prover");

                        assert!($marlin_inst::verify(&index_vk, [c, d], &proof).unwrap());
                        println!("Called verifier");
                        println!("\nShould not verify (i.e. verifier messages should print below):");
                        assert!(!$marlin_inst::verify(&index_vk, [a, a], &proof).unwrap());
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

                            let proof = $marlin_inst::prove_batch(&index_pk, &circuit_batch, rng).unwrap();
                            println!("Called prover");

                            assert!(
                                $marlin_inst::verify_batch(&index_vk, &input_batch, &proof).unwrap(),
                                "Batch verification failed with {batch_size} inputs"
                            );
                            println!("Called verifier");
                            println!("\nShould not verify (i.e. verifier messages should print below):");
                            assert!(
                                !$marlin_inst::verify_batch(
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

                    let rng = &mut test_crypto_rng();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree, rng).unwrap();

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

                    let rng = &mut test_crypto_rng();

                    let max_degree = AHPForR1CS::<Fr, $marlin_mode>::max_degree(100, 25, 300).unwrap();
                    let universal_srs = $marlin_inst::universal_setup(&max_degree, rng).unwrap();

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

mod marlin_recursion {
    use super::*;
    use crate::{
        crypto_hash::PoseidonSponge,
        snark::marlin::{
            ahp::AHPForR1CS,
            fiat_shamir::FiatShamirAlgebraicSpongeRng,
            CircuitVerifyingKey,
            MarlinHidingMode,
            MarlinSNARK,
        },
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_utilities::{
        rand::{test_crypto_rng, Uniform},
        FromBytes,
        ToBytes,
    };

    use core::ops::MulAssign;
    use std::str::FromStr;

    type MarlinInst =
        MarlinSNARK<Bls12_377, FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>, MarlinHidingMode, [Fr]>;

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut test_crypto_rng();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

        for _ in 0..100 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circuit = Circuit { a: Some(a), b: Some(b), num_constraints, num_variables };

            let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &circuit).unwrap();
            println!("Called circuit setup");

            let proof = MarlinInst::prove(&index_pk, &circuit, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&index_vk, [c, d], &proof).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, [a, a], &proof).unwrap());
        }
    }

    fn test_serde_json(num_constraints: usize, num_variables: usize) {
        let rng = &mut test_crypto_rng();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

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
        let rng = &mut test_crypto_rng();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100, 25, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree, rng).unwrap();

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

    // #[test]
    // /// Test on a constraint system that will trigger outlining.
    // fn prove_and_test_outlining() {
    //     let rng = &mut test_crypto_rng();
    //
    //     let universal_srs = MarlinInst::universal_setup(150, 150, 150, rng).unwrap();
    //
    //     let circ = OutlineTestCircuit {
    //         field_phantom: PhantomData,
    //     };
    //
    //     let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();
    //     println!("Called index");
    //
    //     let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
    //     println!("Called prover");
    //
    //     let mut inputs = Vec::new();
    //     for i in 0u128..5u128 {
    //         inputs.push(Fr::from(i));
    //     }
    //
    //     assert!(MarlinInst::verify(&index_vk, &inputs, &proof).unwrap());
    //     println!("Called verifier");
    // }
}
