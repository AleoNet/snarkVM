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

#[cfg(test)]
mod tests {
    use crate::{binding_signature::*, commitment::BHPCommitment, errors::BindingSignatureError, CommitmentScheme};

    use snarkvm_curves::edwards_bls12::EdwardsProjective;
    use snarkvm_utilities::{rand::UniformRand, to_bytes_le, FromBytes, ToBytes};

    use rand::Rng;

    type G = EdwardsProjective;
    type ValueCommitment = BHPCommitment<G, 24, 63>;

    fn generate_random_binding_signature<C: CommitmentScheme, R: Rng>(
        value_comm_pp: &C,
        input_amounts: Vec<u64>,
        output_amounts: Vec<u64>,
        sighash: &[u8],
        rng: &mut R,
    ) -> Result<(Vec<C::Output>, Vec<C::Output>, i64, BindingSignature), BindingSignatureError> {
        let mut value_balance: i64 = 0;

        let mut input_value_commitment_randomness = vec![];
        let mut input_value_commitments = vec![];

        let mut output_value_commitment_randomness = vec![];
        let mut output_value_commitments = vec![];

        for input_amount in input_amounts {
            value_balance += input_amount as i64;

            let value_commit_randomness = C::Randomness::rand(rng);
            let value_commitment =
                value_comm_pp.commit(&input_amount.to_bytes_le().unwrap(), &value_commit_randomness).unwrap();

            input_value_commitment_randomness.push(value_commit_randomness);
            input_value_commitments.push(value_commitment);
        }

        for output_amount in output_amounts {
            value_balance -= output_amount as i64;

            let value_commit_randomness = C::Randomness::rand(rng);
            let value_commitment =
                value_comm_pp.commit(&output_amount.to_bytes_le().unwrap(), &value_commit_randomness).unwrap();

            output_value_commitment_randomness.push(value_commit_randomness);
            output_value_commitments.push(value_commitment);
        }

        let binding_signature = create_binding_signature::<_, G, _>(
            value_comm_pp,
            &input_value_commitments,
            &output_value_commitments,
            &input_value_commitment_randomness,
            &output_value_commitment_randomness,
            value_balance,
            sighash,
            rng,
        )
        .unwrap();

        Ok((input_value_commitments, output_value_commitments, value_balance, binding_signature))
    }

    #[test]
    fn test_value_commitment_binding_signature() {
        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("binding_signature_test");

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);

        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, binding_signature) =
            generate_random_binding_signature::<ValueCommitment, _>(
                &value_comm_pp,
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            )
            .unwrap();

        // Verify the binding signature

        let verified = verify_binding_signature::<ValueCommitment, G>(
            &value_comm_pp,
            &input_value_commitments,
            &output_value_commitments,
            value_balance,
            &sighash,
            &binding_signature,
        )
        .unwrap();

        assert!(verified);
    }

    #[test]
    fn test_binding_signature_byte_conversion() {
        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("binding_signature_test");

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);

        let sighash = [1u8; 64].to_vec();

        let (_, _, _, binding_signature) = generate_random_binding_signature::<ValueCommitment, _>(
            &value_comm_pp,
            vec![input_amount, input_amount_2],
            vec![output_amount, output_amount_2],
            &sighash,
            rng,
        )
        .unwrap();

        let binding_signature_bytes = to_bytes_le![binding_signature].unwrap();
        let reconstructed_binding_signature: BindingSignature =
            FromBytes::read_le(&binding_signature_bytes[..]).unwrap();

        assert_eq!(binding_signature, reconstructed_binding_signature);
    }

    #[test]
    fn test_homomorphism() {
        use snarkvm_curves::{Group, ProjectiveCurve};

        use std::ops::{Add, Neg};

        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("binding_signature_test");

        let mut value_balance = 0;

        let input_amounts = vec![0, 0];
        let output_amounts = vec![0, 0];

        let mut input_value_commitment_randomness = vec![];
        let mut input_value_commitments = vec![];

        let mut output_value_commitment_randomness = vec![];
        let mut output_value_commitments = vec![];

        for input_amount in input_amounts {
            value_balance += input_amount as i64;

            let value_commit_randomness = <ValueCommitment as CommitmentScheme>::Randomness::rand(rng);
            let value_commitment =
                value_comm_pp.commit(&input_amount.to_bytes_le().unwrap(), &value_commit_randomness).unwrap();

            input_value_commitment_randomness.push(value_commit_randomness);
            input_value_commitments.push(value_commitment);
        }

        for output_amount in output_amounts {
            value_balance -= output_amount as i64;

            let value_commit_randomness = <ValueCommitment as CommitmentScheme>::Randomness::rand(rng);
            let value_commitment =
                value_comm_pp.commit(&output_amount.to_bytes_le().unwrap(), &value_commit_randomness).unwrap();

            output_value_commitment_randomness.push(value_commit_randomness);
            output_value_commitments.push(value_commitment);
        }

        /////////////////

        // Calculate the bsk and bvk
        let mut bsk = <G as Group>::ScalarField::default();
        let mut bvk = <G as ProjectiveCurve>::Affine::default();

        for input_vc_randomness in input_value_commitment_randomness {
            let randomness: <G as Group>::ScalarField =
                FromBytes::read_le(&to_bytes_le![input_vc_randomness].unwrap()[..]).unwrap();
            bsk = bsk.add(&randomness);
        }

        for output_vc_randomness in output_value_commitment_randomness {
            let randomness: <G as Group>::ScalarField =
                FromBytes::read_le(&to_bytes_le![output_vc_randomness].unwrap()[..]).unwrap();
            bsk = bsk.add(&randomness.neg());
        }

        for vc_input in input_value_commitments {
            let recovered_input_value_commitment: <G as ProjectiveCurve>::Affine =
                recover_affine_from_x_coord::<G>(&to_bytes_le![vc_input].unwrap()[..]).unwrap();
            bvk = bvk.add(&recovered_input_value_commitment);
        }

        for vc_output in output_value_commitments {
            let recovered_output_value_commitment: <G as ProjectiveCurve>::Affine =
                recover_affine_from_x_coord::<G>(&to_bytes_le![vc_output].unwrap()[..]).unwrap();
            bvk = bvk.add(&recovered_output_value_commitment.neg());
        }

        // Calculate Value balance commitment
        let value_balance_commitment: <G as ProjectiveCurve>::Affine =
            calculate_value_balance_commitment::<ValueCommitment, G>(&value_comm_pp, value_balance).unwrap();

        bvk = bvk.add(&value_balance_commitment.neg());

        // Make sure bvk can be derived from bsk
        let zero: i64 = 0;
        let comm_bsk: <ValueCommitment as CommitmentScheme>::Randomness =
            FromBytes::read_le(&to_bytes_le![bsk].unwrap()[..]).unwrap();
        let expected_bvk_x = to_bytes_le![value_comm_pp.commit(&zero.to_le_bytes(), &comm_bsk).unwrap()].unwrap();
        let expected_bvk = recover_affine_from_x_coord::<G>(&expected_bvk_x).unwrap();
        assert_eq!(bvk, expected_bvk);
    }

    #[test]
    fn test_homomorphism_simple() {
        use snarkvm_curves::{Group, ProjectiveCurve};

        use std::ops::{Add, Neg};

        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("binding_signature_test");

        // Values
        let input_value = 100i64;
        let output_value = 100i64;
        let value_balance = 0i64;

        // Input
        let input_value_commit_randomness = <ValueCommitment as CommitmentScheme>::Randomness::rand(rng);
        let input_value_commitment =
            value_comm_pp.commit(&input_value.to_bytes_le().unwrap(), &input_value_commit_randomness).unwrap();

        // Output
        let output_value_commit_randomness = <ValueCommitment as CommitmentScheme>::Randomness::rand(rng);
        let output_value_commitment =
            value_comm_pp.commit(&output_value.to_bytes_le().unwrap(), &output_value_commit_randomness).unwrap();

        // Calculate Value balance commitment
        let value_balance_commitment: <G as ProjectiveCurve>::Affine =
            calculate_value_balance_commitment::<ValueCommitment, G>(&value_comm_pp, value_balance).unwrap();

        // BVK
        let mut bvk = <G as ProjectiveCurve>::Affine::default();
        bvk = bvk.add(&recover_affine_from_x_coord::<G>(&to_bytes_le![input_value_commitment].unwrap()[..]).unwrap());
        bvk = bvk
            .add(&recover_affine_from_x_coord::<G>(&to_bytes_le![output_value_commitment].unwrap()[..]).unwrap().neg());
        bvk = bvk.add(
            &recover_affine_from_x_coord::<G>(&to_bytes_le![value_balance_commitment].unwrap()[..]).unwrap().neg(),
        );

        // BSK
        let mut bsk = <G as Group>::ScalarField::default();
        bsk = bsk.add(&input_value_commit_randomness);
        bsk = bsk.add(&output_value_commit_randomness.neg());

        // Make sure bvk can be derived from bsk
        let zero: i64 = 0;
        let expected_bvk_x = to_bytes_le![value_comm_pp.commit(&zero.to_le_bytes(), &bsk).unwrap()].unwrap();
        let expected_bvk = recover_affine_from_x_coord::<G>(&expected_bvk_x).unwrap();
        assert_eq!(bvk, expected_bvk);
    }

    #[test]
    fn test_homomorphism_simplest() {
        use snarkvm_curves::{Group, ProjectiveCurve};
        use snarkvm_fields::Zero;
        use std::ops::{Add, Neg};

        // Setup parameters
        let value_comm_pp = BHPCommitment::<EdwardsProjective, 24, 63>::setup("binding_signature_test");

        // Values
        let input_value = 0i64;
        let output_value = 0i64;
        let value_balance = 0i64;

        let zero_randomness = <ValueCommitment as CommitmentScheme>::Randomness::zero();

        // Input
        let input_value_commitment =
            value_comm_pp.commit(&input_value.to_bytes_le().unwrap(), &zero_randomness).unwrap();

        // Output
        let output_value_commitment =
            value_comm_pp.commit(&output_value.to_bytes_le().unwrap(), &zero_randomness).unwrap();

        // Calculate Value balance commitment
        // let value_balance_commitment =
        //     value_comm_pp.commit(&value_balance.to_bytes_le().unwrap(), &zero_randomness).unwrap();

        // BVK
        let mut bvk = <G as ProjectiveCurve>::Affine::default();
        bvk = bvk.add(&recover_affine_from_x_coord::<G>(&to_bytes_le![input_value_commitment].unwrap()[..]).unwrap());
        bvk = bvk.add(&recover_affine_from_x_coord::<G>(&to_bytes_le![output_value_commitment].unwrap()[..]).unwrap());
        // bvk = bvk.add(
        //     &recover_affine_from_x_coord::<G>(&to_bytes_le![value_balance_commitment].unwrap()[..]).unwrap().neg(),
        // );

        // Make sure bvk can be derived from bsk
        // let zero: i64 = 0;
        let expected_bvk_x =
            to_bytes_le![value_comm_pp.commit(&value_balance.to_le_bytes(), &zero_randomness).unwrap()].unwrap();
        let expected_bvk = recover_affine_from_x_coord::<G>(&expected_bvk_x).unwrap();
        assert_eq!(bvk, expected_bvk);
    }
}
