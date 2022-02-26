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

use crate::{error::ValueBalanceCommitmentError, Network};
use snarkvm_algorithms::CommitmentScheme;
use snarkvm_curves::AffineCurve;
use snarkvm_fields::{Field, One, Zero};
use snarkvm_utilities::{BitIteratorLE, FromBytes, ToBytes};

use blake2::{
    digest::{Update, VariableOutput},
    Blake2bVar,
};
use rand::Rng;
use std::{
    io::{Read, Result as IoResult, Write},
    ops::{Add, Mul, Neg},
};

pub fn hash_into_field<N: Network>(a: &[u8], b: &[u8]) -> N::ProgramScalarField {
    let mut hasher = Blake2bVar::new(64).unwrap();
    hasher.update(a);
    hasher.update(b);

    let mut hash = [0u8; 64];
    hasher.finalize_variable(&mut hash).unwrap();

    let hash_u64_repr: Vec<u64> = hash
        .chunks(8)
        .map(|chunk| {
            let mut fixed_size = [0u8; 8];
            fixed_size.copy_from_slice(chunk);
            u64::from_le_bytes(fixed_size)
        })
        .collect();

    // Scaling by random cofactor for the scalar field
    let mut res = N::ProgramScalarField::one();
    for bit in BitIteratorLE::new(hash_u64_repr) {
        res.double_in_place();
        if bit {
            res = res.add(&res)
        }
    }

    res
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct ValueBalanceCommitment<N: Network> {
    pub rbar: N::ProgramAffineCurve,
    pub sbar: N::ProgramScalarField,
}

impl<N: Network> ToBytes for ValueBalanceCommitment<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.rbar.to_x_coordinate().write_le(&mut writer)?;
        self.sbar.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for ValueBalanceCommitment<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = <N::ProgramAffineCurve as AffineCurve>::BaseField::read_le(&mut reader)?;

        if let Some(rbar) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, false) {
            if rbar.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self { rbar, sbar: FromBytes::read_le(&mut reader)? });
            }
        }

        if let Some(rbar) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, true) {
            if rbar.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self { rbar, sbar: FromBytes::read_le(&mut reader)? });
            }
        }

        Err(ValueBalanceCommitmentError::NotInCorrectSubgroupOnCurve.into())
    }
}

pub fn commit_value_balance<N: Network, R: Rng>(
    input_value_commitments: &Vec<N::ProgramAffineCurve>,
    output_value_commitments: &Vec<N::ProgramAffineCurve>,
    input_value_commitment_randomness: &Vec<N::ProgramScalarField>,
    output_value_commitment_randomness: &Vec<N::ProgramScalarField>,
    value_balance: i64,
    input: &[u8],
    rng: &mut R,
) -> Result<ValueBalanceCommitment<N>, ValueBalanceCommitmentError> {
    // Calculate the bsk and bvk
    let mut bsk = N::ProgramScalarField::zero();

    for input_vc_randomness in input_value_commitment_randomness {
        bsk += input_vc_randomness;
    }

    for output_vc_randomness in output_value_commitment_randomness {
        bsk -= output_vc_randomness;
    }

    let mut bvk = N::ProgramAffineCurve::zero();

    for vc_input in input_value_commitments {
        bvk += vc_input;
    }

    for vc_output in output_value_commitments {
        bvk -= vc_output;
    }

    // Calculate the value balance commitment.
    bvk -= calculate_value_balance_commitment::<N>(value_balance)?;

    // Make sure bvk can be derived from bsk
    let expected_bvk = N::value_commitment().commit(&0i64.to_le_bytes(), &bsk)?;
    assert_eq!(bvk, expected_bvk);

    // Generate randomness
    let mut sig_rand = [0u8; 80];
    rng.fill(&mut sig_rand[..]);

    // Generate signature using message

    let r_edwards = hash_into_field::<N>(&sig_rand[..], input);
    let rbar = N::value_commitment().commit(&0i64.to_le_bytes(), &r_edwards)?;

    let mut sbar = hash_into_field::<N>(&rbar.to_x_coordinate().to_bytes_le()?, input);
    sbar = sbar.mul(&bsk);
    sbar = sbar.add(&r_edwards);

    Ok(ValueBalanceCommitment { rbar, sbar })
}

pub fn verify_value_balance_commitment<N: Network>(
    input_value_commitments: &Vec<N::ProgramAffineCurve>,
    output_value_commitments: &Vec<N::ProgramAffineCurve>,
    value_balance: i64,
    input: &[u8],
    signature: &ValueBalanceCommitment<N>,
) -> Result<bool, ValueBalanceCommitmentError> {
    // Craft verifying key
    let mut bvk = N::ProgramAffineCurve::zero();

    for vc_input in input_value_commitments {
        bvk += vc_input;
    }

    for vc_output in output_value_commitments {
        bvk -= vc_output;
    }

    // Calculate the value balance commitment.
    bvk -= calculate_value_balance_commitment::<N>(value_balance)?;

    // Verify the signature
    let c = hash_into_field::<N>(&signature.rbar.to_x_coordinate().to_bytes_le()?, input);

    let recommit = N::value_commitment().commit(&0i64.to_le_bytes(), &signature.sbar)?;

    Ok((bvk.mul(c) + signature.rbar - recommit).is_zero())
}

/// Returns the value balance commitment as `value_balance.sign() * Commit(value_balance.abs(), randomness)`.
pub fn calculate_value_balance_commitment<N: Network>(
    value_balance: i64,
) -> Result<N::ProgramAffineCurve, ValueBalanceCommitmentError> {
    // Convert the value balance to an absolute u64.
    let value_balance_as_u64 = match value_balance.checked_abs() {
        Some(val) => val as u64,
        None => return Err(ValueBalanceCommitmentError::OutOfBounds(value_balance)),
    };

    // Compute the value balance commitment.
    let zero_randomness = Zero::zero();
    let value_balance_commitment =
        N::value_commitment().commit(&value_balance_as_u64.to_le_bytes(), &zero_randomness)?;

    match value_balance.is_negative() {
        true => Ok(value_balance_commitment.neg()),
        false => Ok(value_balance_commitment),
    }
}

pub fn gadget_verification_setup<N: Network>(
    input_value_commitments: &[N::ProgramAffineCurve],
    output_value_commitments: &[N::ProgramAffineCurve],
    input: &[u8],
    signature: &ValueBalanceCommitment<N>,
) -> Result<
    (N::ProgramScalarField, N::ProgramAffineCurve, N::ProgramAffineCurve, N::ProgramAffineCurve),
    ValueBalanceCommitmentError,
> {
    // Craft the partial verifying key
    let mut partial_bvk = N::ProgramAffineCurve::zero();

    for vc_input in input_value_commitments {
        partial_bvk += vc_input;
    }

    for vc_output in output_value_commitments {
        partial_bvk -= vc_output;
    }

    let c = hash_into_field::<N>(&signature.rbar.to_x_coordinate().to_bytes_le()?, input);
    let recommit = N::value_commitment().commit(&0i64.to_le_bytes(), &signature.sbar)?;

    Ok((c, partial_bvk, signature.rbar, recommit))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::testnet2::Testnet2;
    use snarkvm_algorithms::CommitmentScheme;
    use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

    use rand::Rng;

    pub(crate) fn generate_random_value_balance_commitment<N: Network, R: Rng>(
        input_amounts: Vec<u64>,
        output_amounts: Vec<u64>,
        sighash: &[u8],
        rng: &mut R,
    ) -> (Vec<N::ProgramAffineCurve>, Vec<N::ProgramAffineCurve>, i64, ValueBalanceCommitment<N>) {
        let mut value_balance: i64 = 0;

        let mut input_value_commitment_randomness = vec![];
        let mut input_value_commitments = vec![];

        let mut output_value_commitment_randomness = vec![];
        let mut output_value_commitments = vec![];

        for input_amount in input_amounts {
            value_balance += input_amount as i64;

            let value_commit_randomness = UniformRand::rand(rng);
            let value_commitment =
                N::value_commitment().commit(&input_amount.to_le_bytes(), &value_commit_randomness).unwrap();

            input_value_commitment_randomness.push(value_commit_randomness);
            input_value_commitments.push(value_commitment);
        }

        for output_amount in output_amounts {
            value_balance -= output_amount as i64;

            let value_commit_randomness = UniformRand::rand(rng);
            let value_commitment =
                N::value_commitment().commit(&output_amount.to_le_bytes(), &value_commit_randomness).unwrap();

            output_value_commitment_randomness.push(value_commit_randomness);
            output_value_commitments.push(value_commitment);
        }

        let value_balance_commitment = commit_value_balance::<N, _>(
            &input_value_commitments,
            &output_value_commitments,
            &input_value_commitment_randomness,
            &output_value_commitment_randomness,
            value_balance,
            sighash,
            rng,
        )
        .unwrap();

        (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment)
    }

    #[test]
    fn test_value_balance_commitment() {
        let rng = &mut rand::thread_rng();

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);
        let sighash = [1u8; 64].to_vec();

        let (input_value_commitments, output_value_commitments, value_balance, value_balance_commitment) =
            generate_random_value_balance_commitment::<Testnet2, _>(
                vec![input_amount, input_amount_2],
                vec![output_amount, output_amount_2],
                &sighash,
                rng,
            );

        // Verify the value balance commitment
        assert!(
            verify_value_balance_commitment::<Testnet2>(
                &input_value_commitments,
                &output_value_commitments,
                value_balance,
                &sighash,
                &value_balance_commitment,
            )
            .unwrap()
        );
    }

    #[test]
    fn test_value_balance_commitment_serialization() {
        let rng = &mut rand::thread_rng();

        let input_amount: u64 = rng.gen_range(0..100000000);
        let input_amount_2: u64 = rng.gen_range(0..100000000);
        let output_amount: u64 = rng.gen_range(0..100000000);
        let output_amount_2: u64 = rng.gen_range(0..100000000);
        let sighash = [1u8; 64].to_vec();

        let (_, _, _, value_balance_commitment) = generate_random_value_balance_commitment::<Testnet2, _>(
            vec![input_amount, input_amount_2],
            vec![output_amount, output_amount_2],
            &sighash,
            rng,
        );

        let reconstructed_value_balance_commitment: ValueBalanceCommitment<_> =
            FromBytes::read_le(&*value_balance_commitment.to_bytes_le().unwrap()).unwrap();

        assert_eq!(value_balance_commitment, reconstructed_value_balance_commitment);
    }
}
