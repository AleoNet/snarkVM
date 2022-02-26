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

use crate::error::ValueBalanceCommitmentError;
use snarkvm_algorithms::CommitmentScheme;
use snarkvm_curves::{AffineCurve, Group, ProjectiveCurve};
use snarkvm_fields::{Field, One, Zero};
use snarkvm_utilities::{
    bititerator::BitIteratorLE,
    bytes::{FromBytes, ToBytes},
    to_bytes_le,
};

use blake2::{
    digest::{Update, VariableOutput},
    Blake2bVar,
};
use rand::Rng;
use std::{
    io::{Read, Result as IoResult, Write},
    ops::{Add, Mul, Neg},
};

// TODO (raychu86): Refactor all of this into formal structs and add documentation.

pub fn hash_into_field<G: Group + ProjectiveCurve>(a: &[u8], b: &[u8]) -> <G as Group>::ScalarField {
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
    let mut res = <G as Group>::ScalarField::one();
    for bit in BitIteratorLE::new(hash_u64_repr) {
        res.double_in_place();
        if bit {
            res = res.add(&res)
        }
    }

    res
}

pub fn recover_affine_from_x_coord<G: Group + ProjectiveCurve>(
    x_bytes: &[u8],
) -> Result<<G as ProjectiveCurve>::Affine, ValueBalanceCommitmentError> {
    let x: <<G as ProjectiveCurve>::Affine as AffineCurve>::BaseField = FromBytes::read_le(x_bytes)?;

    if let Some(affine) = <G as ProjectiveCurve>::Affine::from_x_coordinate(x, false) {
        if affine.is_in_correct_subgroup_assuming_on_curve() {
            return Ok(affine);
        }
    }

    if let Some(affine) = <G as ProjectiveCurve>::Affine::from_x_coordinate(x, true) {
        if affine.is_in_correct_subgroup_assuming_on_curve() {
            return Ok(affine);
        }
    }

    Err(ValueBalanceCommitmentError::NotInCorrectSubgroupOnCurve(to_bytes_le![x]?))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct ValueBalanceCommitment<G: Group + ProjectiveCurve> {
    pub rbar: <<G as ProjectiveCurve>::Affine as AffineCurve>::BaseField,
    pub sbar: <G as Group>::ScalarField,
}

impl<G: Group + ProjectiveCurve> ToBytes for ValueBalanceCommitment<G> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.rbar.write_le(&mut writer)?;
        self.sbar.write_le(&mut writer)
    }
}

impl<G: Group + ProjectiveCurve> FromBytes for ValueBalanceCommitment<G> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { rbar: FromBytes::read_le(&mut reader)?, sbar: FromBytes::read_le(&mut reader)? })
    }
}

pub fn commit_value_balance<C: CommitmentScheme, G: Group + ProjectiveCurve, R: Rng>(
    value_commitment: &C,
    input_value_commitments: &Vec<C::Output>,
    output_value_commitments: &Vec<C::Output>,
    input_value_commitment_randomness: &Vec<C::Randomness>,
    output_value_commitment_randomness: &Vec<C::Randomness>,
    value_balance: i64,
    input: &[u8],
    rng: &mut R,
) -> Result<ValueBalanceCommitment<G>, ValueBalanceCommitmentError> {
    // Calculate the bsk and bvk
    let mut bsk = <G as Group>::ScalarField::default();
    let mut bvk = <G as ProjectiveCurve>::Affine::default();

    for input_vc_randomness in input_value_commitment_randomness {
        let randomness: <G as Group>::ScalarField = FromBytes::read_le(&to_bytes_le![input_vc_randomness]?[..])?;
        bsk = bsk.add(&randomness);
    }

    for output_vc_randomness in output_value_commitment_randomness {
        let randomness: <G as Group>::ScalarField = FromBytes::read_le(&to_bytes_le![output_vc_randomness]?[..])?;
        bsk = bsk.add(&randomness.neg());
    }

    for vc_input in input_value_commitments {
        let recovered_input_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_input]?[..])?;
        bvk = bvk.add(&recovered_input_value_commitment);
    }

    for vc_output in output_value_commitments {
        let recovered_output_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_output]?[..])?;
        bvk = bvk.add(&recovered_output_value_commitment.neg());
    }

    // Calculate Value balance commitment
    let value_balance_commitment: <G as ProjectiveCurve>::Affine =
        calculate_value_balance_commitment::<C, G>(value_commitment, value_balance)?;

    bvk = bvk.add(&value_balance_commitment.neg());

    // Make sure bvk can be derived from bsk
    let zero: i64 = 0;
    let comm_bsk: C::Randomness = FromBytes::read_le(&to_bytes_le![bsk]?[..])?;
    let expected_bvk_x = to_bytes_le![value_commitment.commit(&zero.to_le_bytes(), &comm_bsk)?]?;
    let expected_bvk = recover_affine_from_x_coord::<G>(&expected_bvk_x)?;
    assert_eq!(bvk, expected_bvk);

    // Generate randomness
    let mut sig_rand = [0u8; 80];
    rng.fill(&mut sig_rand[..]);

    // Generate signature using message

    let r_edwards: <G as Group>::ScalarField = hash_into_field::<G>(&sig_rand[..], input);
    let r: C::Randomness = FromBytes::read_le(&to_bytes_le![r_edwards]?[..])?;
    let r_g = value_commitment.commit(&zero.to_le_bytes(), &r)?;

    let mut rbar = [0u8; 32];
    r_g.write_le(&mut rbar[..])?;

    let mut s: <G as Group>::ScalarField = hash_into_field::<G>(&rbar[..], input);
    s = s.mul(&bsk);
    s = s.add(&r_edwards);

    let mut sbar = [0u8; 32];
    sbar.copy_from_slice(&to_bytes_le![s]?[..]);

    Ok(FromBytes::from_bytes_le(&[rbar, sbar].concat())?)
}

pub fn verify_value_balance_commitment<C: CommitmentScheme, G: Group + ProjectiveCurve>(
    value_commitment: &C,
    input_value_commitments: &Vec<C::Output>,
    output_value_commitments: &Vec<C::Output>,
    value_balance: i64,
    input: &[u8],
    signature: &ValueBalanceCommitment<G>,
) -> Result<bool, ValueBalanceCommitmentError> {
    // Craft verifying key
    let mut bvk: <G as ProjectiveCurve>::Affine = <G as ProjectiveCurve>::Affine::default();

    for vc_input in input_value_commitments {
        let recovered_input_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_input]?[..])?;
        bvk = bvk.add(&recovered_input_value_commitment);
    }

    for vc_output in output_value_commitments {
        let recovered_output_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_output]?[..])?;
        bvk = bvk.add(&recovered_output_value_commitment.neg());
    }

    // Calculate Value balance commitment
    let value_balance_commitment: <G as ProjectiveCurve>::Affine =
        calculate_value_balance_commitment::<C, G>(value_commitment, value_balance)?;

    bvk = bvk.add(&value_balance_commitment.neg());

    // Verify the signature
    let c: <G as Group>::ScalarField = hash_into_field::<G>(&signature.rbar.to_bytes_le()?, input);
    let affine_r = recover_affine_from_x_coord::<G>(&signature.rbar.to_bytes_le()?)?;

    let zero: i64 = 0;
    let s: C::Randomness = FromBytes::read_le(&*signature.sbar.to_bytes_le()?)?;
    let recommit = to_bytes_le![value_commitment.commit(&zero.to_le_bytes(), &s)?]?;
    let recovered_recommit = recover_affine_from_x_coord::<G>(&recommit)?;

    let check_verification = bvk.mul(c).add(&affine_r).add(&recovered_recommit.neg());

    Ok(check_verification.is_zero())
}

/// Returns the value balance commitment as `value_balance.sign() * Commit(value_balance.abs(), randomness)`.
pub fn calculate_value_balance_commitment<C: CommitmentScheme, G: Group + ProjectiveCurve>(
    value_commitment: &C,
    value_balance: i64,
) -> Result<<G as ProjectiveCurve>::Affine, ValueBalanceCommitmentError> {
    let value_balance_as_u64 = match value_balance.checked_abs() {
        Some(val) => val as u64,
        None => return Err(ValueBalanceCommitmentError::OutOfBounds(value_balance)),
    };

    let zero_randomness = C::Randomness::default();
    let value_balance_commitment =
        to_bytes_le![value_commitment.commit(&value_balance_as_u64.to_le_bytes(), &zero_randomness)?]?;

    let recovered_value_balance_commitment: <G as ProjectiveCurve>::Affine =
        recover_affine_from_x_coord::<G>(&value_balance_commitment)?;

    match value_balance.is_negative() {
        true => Ok(recovered_value_balance_commitment.neg()),
        false => Ok(recovered_value_balance_commitment),
    }
}

pub fn gadget_verification_setup<C: CommitmentScheme, G: Group + ProjectiveCurve>(
    value_commitment: &C,
    input_value_commitments: &[C::Output],
    output_value_commitments: &[C::Output],
    input: &[u8],
    signature: &ValueBalanceCommitment<G>,
) -> Result<(C::Randomness, G, G, G), ValueBalanceCommitmentError> {
    // Craft the partial verifying key
    let mut partial_bvk = <G as ProjectiveCurve>::Affine::default();

    for vc_input in input_value_commitments {
        let recovered_input_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_input]?[..])?;
        partial_bvk = partial_bvk.add(&recovered_input_value_commitment);
    }

    for vc_output in output_value_commitments {
        let recovered_output_value_commitment: <G as ProjectiveCurve>::Affine =
            recover_affine_from_x_coord::<G>(&to_bytes_le![vc_output]?[..])?;
        partial_bvk = partial_bvk.add(&recovered_output_value_commitment.neg());
    }

    let c_field: <G as Group>::ScalarField = hash_into_field::<G>(&signature.rbar.to_bytes_le()?, input);
    let c: C::Randomness = FromBytes::read_le(&to_bytes_le![c_field]?[..])?;

    let affine_r = recover_affine_from_x_coord::<G>(&signature.rbar.to_bytes_le()?)?;

    let zero: i64 = 0;
    let s: C::Randomness = FromBytes::read_le(&*signature.sbar.to_bytes_le()?)?;
    let recommit = to_bytes_le![value_commitment.commit(&zero.to_le_bytes(), &s)?]?;
    let recovered_recommit = recover_affine_from_x_coord::<G>(&recommit).unwrap();

    let partial_bvk: G = FromBytes::read_le(&to_bytes_le![partial_bvk.into_projective()]?[..])?;
    let affine_r: G = FromBytes::read_le(&to_bytes_le![affine_r.into_projective()]?[..])?;
    let recovered_recommit: G = FromBytes::read_le(&to_bytes_le![recovered_recommit.into_projective()]?[..])?;

    Ok((c, partial_bvk, affine_r, recovered_recommit))
}

#[cfg(test)]
mod value_balance_commitment_tests {
    use super::*;
    use snarkvm_algorithms::{commitment::PedersenCompressedCommitment, CommitmentScheme};
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
    ) -> Result<(Vec<C::Output>, Vec<C::Output>, i64, ValueBalanceCommitment<G>), ValueBalanceCommitmentError> {
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
        let reconstructed_value_balance_commitment: ValueBalanceCommitment<_> =
            FromBytes::read_le(&value_balance_commitment_bytes[..]).unwrap();

        assert_eq!(value_balance_commitment, reconstructed_value_balance_commitment);
    }
}
