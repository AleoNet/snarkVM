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

use crate::{
    binding_signature::*,
    commitment::PedersenCompressedCommitment,
    errors::BindingSignatureError,
    CommitmentScheme,
};

use snarkvm_curves::edwards_bls12::EdwardsProjective;
use snarkvm_utilities::{rand::UniformRand, to_bytes_le, FromBytes, ToBytes};

use rand::Rng;

type G = EdwardsProjective;
type ValueCommitment = PedersenCompressedCommitment<G, 4, 350>;

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
    let reconstructed_binding_signature: BindingSignature = FromBytes::read_le(&binding_signature_bytes[..]).unwrap();

    assert_eq!(binding_signature, reconstructed_binding_signature);
}
