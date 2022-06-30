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

use snarkvm_fields::{Field, Zero};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

struct MySillyCircuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for MySillyCircuit<ConstraintF> {
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

        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);
        cs.enforce(|| "a*b=c", |lc| lc + a, |lc| lc + b, |lc| lc + c);

        Ok(())
    }
}

mod bls12_377 {
    use super::*;
    use crate::snark::groth16::{
        create_proof_no_zk,
        create_random_proof,
        generate_random_parameters,
        prepare_verifying_key,
        verify_proof,
        Proof,
    };
    use snarkvm_curves::bls12_377::{Bls12_377, Fr};
    use snarkvm_utilities::{str::FromStr, FromBytes, ToBytes, UniformRand};

    use rand::thread_rng;

    #[test]
    fn prove_and_verify() {
        let rng = &mut thread_rng();
        let parameters =
            generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

        for _ in 0..100 {
            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            let c = a * b;

            let proof = create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap();
            let pvk = prepare_verifying_key::<Bls12_377>(parameters.vk.clone());

            assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
            assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
        }
    }

    #[test]
    fn test_prove_and_verify_no_zk() {
        let rng = &mut thread_rng();
        let parameters =
            generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

        for _ in 0..100 {
            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            let c = a * b;

            let proof = create_proof_no_zk(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters).unwrap();
            let pvk = prepare_verifying_key::<Bls12_377>(parameters.vk.clone());

            assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
            assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
        }
    }

    #[test]
    fn test_serde_json() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Serialize
        let expected_string = &expected_proof.to_string();
        let candidate_string = serde_json::to_string(&expected_proof).unwrap();
        assert_eq!(388, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_proof, serde_json::from_str(&candidate_string).unwrap());
        assert_eq!(expected_proof, Proof::from_str(expected_string).unwrap());
    }

    #[test]
    fn test_bincode_compressed() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Serialize
        let expected_bytes = expected_proof.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_proof).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        assert_eq!(expected_proof, Proof::read_le(&expected_bytes[..]).unwrap());
    }

    #[test]
    fn test_bincode_uncompressed() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Uncompressed bytes.
        let mut expected_bytes = Vec::new();
        expected_proof.write_uncompressed(&mut expected_bytes).unwrap();

        // Deserialize
        assert_eq!(expected_proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        assert_eq!(expected_proof, Proof::read_le(&expected_bytes[..]).unwrap());
    }
}

mod bw6_761 {
    use super::*;
    use crate::snark::groth16::{
        create_random_proof,
        generate_random_parameters,
        prepare_verifying_key,
        verify_proof,
        Proof,
    };
    use snarkvm_curves::bw6_761::{Fr, BW6_761};
    use snarkvm_utilities::{rand::UniformRand, str::FromStr, FromBytes, ToBytes};

    use rand::thread_rng;

    #[test]
    fn prove_and_verify() {
        let rng = &mut thread_rng();
        let parameters =
            generate_random_parameters::<BW6_761, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

        let (a, b) = (Fr::rand(rng), Fr::rand(rng));
        let c = a * b;

        let proof = create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap();
        let pvk = prepare_verifying_key::<BW6_761>(parameters.vk);

        assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
        assert!(!verify_proof(&pvk, &proof, &[Fr::zero()]).unwrap());
    }

    #[test]
    fn test_serde_json() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<BW6_761, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Serialize
        let expected_string = &expected_proof.to_string();
        let candidate_string = serde_json::to_string(&expected_proof).unwrap();
        assert_eq!(580, candidate_string.len(), "Update me if serialization has changed");
        assert_eq!(
            expected_string,
            serde_json::Value::from_str(&candidate_string)
                .unwrap()
                .as_str()
                .unwrap()
        );

        // Deserialize
        assert_eq!(expected_proof, serde_json::from_str(&candidate_string).unwrap());
        assert_eq!(expected_proof, Proof::from_str(expected_string).unwrap());
    }

    #[test]
    fn test_bincode_compressed() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<BW6_761, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Serialize
        let expected_bytes = expected_proof.to_bytes_le().unwrap();
        assert_eq!(&expected_bytes[..], &bincode::serialize(&expected_proof).unwrap()[..]);

        // Deserialize
        assert_eq!(expected_proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        assert_eq!(expected_proof, Proof::read_le(&expected_bytes[..]).unwrap());
    }

    #[test]
    fn test_bincode_uncompressed() {
        let expected_proof = {
            let rng = &mut thread_rng();
            let parameters =
                generate_random_parameters::<BW6_761, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

            let (a, b) = (Fr::rand(rng), Fr::rand(rng));
            create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap()
        };

        // Uncompressed bytes.
        let mut expected_bytes = Vec::new();
        expected_proof.write_uncompressed(&mut expected_bytes).unwrap();

        // Deserialize
        assert_eq!(expected_proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        assert_eq!(expected_proof, Proof::read_le(&expected_bytes[..]).unwrap());
    }
}

mod serialization {
    use super::*;
    use crate::snark::groth16::{create_random_proof, generate_random_parameters, Proof};
    use snarkvm_curves::bls12_377::{Bls12_377, Fr};
    use snarkvm_utilities::{
        rand::{test_rng, UniformRand},
        FromBytes,
        ToBytes,
    };

    #[test]
    fn test_canonical_compressed() {
        let rng = &mut test_rng();
        let parameters =
            generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

        let (a, b) = (Fr::rand(rng), Fr::rand(rng));
        let proof = create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap();

        // Serialize
        let compressed_serialization = proof.to_bytes_le().unwrap();
        assert_eq!(
            Proof::<Bls12_377>::compressed_proof_size().unwrap(),
            compressed_serialization.len()
        );
        assert!(Proof::<Bls12_377>::read_uncompressed(&compressed_serialization[..]).is_err());

        // Deserialize
        let recovered_proof: Proof<Bls12_377> = FromBytes::read_le(&compressed_serialization[..]).unwrap();
        assert!(recovered_proof.compressed);
    }

    #[test]
    fn test_canonical_uncompressed() {
        let rng = &mut test_rng();
        let parameters =
            generate_random_parameters::<Bls12_377, _, _>(&MySillyCircuit { a: None, b: None }, rng).unwrap();

        let (a, b) = (Fr::rand(rng), Fr::rand(rng));
        let proof = create_random_proof(&MySillyCircuit { a: Some(a), b: Some(b) }, &parameters, rng).unwrap();

        // Serialize
        let mut uncompressed_serialization = Vec::new();
        proof.write_uncompressed(&mut uncompressed_serialization).unwrap();
        assert_eq!(
            Proof::<Bls12_377>::uncompressed_proof_size().unwrap(),
            uncompressed_serialization.len()
        );
        assert!(Proof::<Bls12_377>::read_compressed(&uncompressed_serialization[..]).is_err());

        // Deserialize
        let recovered_proof: Proof<Bls12_377> = FromBytes::read_le(&uncompressed_serialization[..]).unwrap();
        assert!(!recovered_proof.compressed);
    }
}
