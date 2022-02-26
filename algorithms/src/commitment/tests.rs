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
    commitment::{BHPCommitment, PedersenCommitment, PedersenCompressedCommitment},
    traits::CommitmentScheme,
};
use snarkvm_curves::edwards_bls12::EdwardsProjective;

const PEDERSEN_NUM_WINDOWS: usize = 8;
const PEDERSEN_WINDOW_SIZE: usize = 128;

const BHP_NUM_WINDOWS: usize = 32;
const BHP_WINDOW_SIZE: usize = 48;

fn commitment_parameters_serialization<C: CommitmentScheme>() {
    let commitment = C::setup("commitment_parameters_serialization").to_bytes_le().unwrap();
    let recovered_commitment = C::read_le(&commitment[..]).unwrap();
    assert_eq!(commitment, recovered_commitment.to_bytes_le().unwrap());
}

#[test]
fn bhp_commitment_parameters_serialization() {
    commitment_parameters_serialization::<BHPCommitment<EdwardsProjective, BHP_NUM_WINDOWS, BHP_WINDOW_SIZE>>();
}

#[test]
fn pedersen_commitment_parameters_serialization() {
    commitment_parameters_serialization::<
        PedersenCommitment<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>,
    >();
}

#[test]
fn pedersen_compressed_commitment_parameters_serialization() {
    commitment_parameters_serialization::<
        PedersenCompressedCommitment<EdwardsProjective, PEDERSEN_NUM_WINDOWS, PEDERSEN_WINDOW_SIZE>,
    >();
}

mod value_balance_commitment_tests {
    use crate::{
        commitment::{value_balance::*, PedersenCompressedCommitment},
        errors::ValueBalanceCommitmentError,
        CommitmentScheme,
    };

    use snarkvm_curves::edwards_bls12::EdwardsProjective;
    use snarkvm_utilities::{rand::UniformRand, to_bytes_le, FromBytes, ToBytes};

    use rand::Rng;

    type G = EdwardsProjective;
    type ValueCommitment = PedersenCompressedCommitment<G, 4, 350>;

    fn generate_random_value_balance_commitment<C: CommitmentScheme, R: Rng>(
        value_comm_pp: &C,
        input_amounts: Vec<u64>,
        output_amounts: Vec<u64>,
        sighash: &[u8],
        rng: &mut R,
    ) -> Result<(Vec<C::Output>, Vec<C::Output>, i64, ValueBalanceCommitment), ValueBalanceCommitmentError> {
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

        let value_balance_commitment = commit_value_balance::<_, G, _>(
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

        Ok((input_value_commitments, output_value_commitments, value_balance, value_balance_commitment))
    }

    #[test]
    fn test_value_commitment_commitment() {
        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("value_balance_commitment_test");

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);

        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment) =
            generate_random_value_balance_commitment::<ValueCommitment, _>(
                &value_comm_pp,
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            )
            .unwrap();

        // Verify the value balance commitment

        let verified = verify_value_balance_commitment::<ValueCommitment, G>(
            &value_comm_pp,
            &input_value_commitments,
            &output_value_commitments,
            value_balance,
            &sighash,
            &value_balance_commitment,
        )
        .unwrap();

        assert!(verified);
    }

    #[test]
    fn test_value_balance_commitment_serialization() {
        let rng = &mut rand::thread_rng();

        // Setup parameters

        let value_comm_pp = ValueCommitment::setup("value_balance_commitment_test");

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);

        let sighash = [1u8; 64].to_vec();

        let (_, _, _, value_balance_commitment) = generate_random_value_balance_commitment::<ValueCommitment, _>(
            &value_comm_pp,
            vec![input_amount, input_amount_2],
            vec![output_amount, output_amount_2],
            &sighash,
            rng,
        )
        .unwrap();

        let value_balance_commitment_bytes = to_bytes_le![value_balance_commitment].unwrap();
        let reconstructed_value_balance_commitment: ValueBalanceCommitment =
            FromBytes::read_le(&value_balance_commitment_bytes[..]).unwrap();

        assert_eq!(value_balance_commitment, reconstructed_value_balance_commitment);
    }
}
