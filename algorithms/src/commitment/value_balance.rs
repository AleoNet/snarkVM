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

use crate::{errors::ValueBalanceCommitmentError, CommitmentScheme};
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

// Binding signature scheme derived from Zcash's redDSA
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueBalanceCommitment {
    pub rbar: Vec<u8>,
    pub sbar: Vec<u8>,
}

impl ValueBalanceCommitment {
    pub fn new(rbar: Vec<u8>, sbar: Vec<u8>) -> Result<Self, ValueBalanceCommitmentError> {
        assert_eq!(rbar.len(), 32);
        assert_eq!(sbar.len(), 32);

        Ok(Self { rbar, sbar })
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&self.rbar[..]);
        bytes.extend_from_slice(&self.sbar[..]);

        bytes
    }

    pub fn from_bytes<G: Group + ProjectiveCurve>(
        signature_bytes: Vec<u8>,
    ) -> Result<Self, ValueBalanceCommitmentError> {
        assert_eq!(signature_bytes.len(), 64);

        let rbar = signature_bytes[0..32].to_vec();
        let sbar = signature_bytes[32..64].to_vec();

        let _rbar: <<G as ProjectiveCurve>::Affine as AffineCurve>::BaseField = FromBytes::read_le(&rbar[..])?;
        let _sbar: <G as Group>::ScalarField = FromBytes::read_le(&sbar[..])?;

        Ok(Self { rbar, sbar })
    }
}

impl ToBytes for ValueBalanceCommitment {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.rbar.write_le(&mut writer)?;
        self.sbar.write_le(&mut writer)
    }
}

impl FromBytes for ValueBalanceCommitment {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let rbar: [u8; 32] = FromBytes::read_le(&mut reader)?;
        let sbar: [u8; 32] = FromBytes::read_le(&mut reader)?;

        Ok(Self { rbar: rbar.to_vec(), sbar: sbar.to_vec() })
    }
}

impl Default for ValueBalanceCommitment {
    #[inline]
    fn default() -> Self {
        Self { rbar: [0u8; 32].to_vec(), sbar: [0u8; 32].to_vec() }
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
) -> Result<ValueBalanceCommitment, ValueBalanceCommitmentError> {
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

    ValueBalanceCommitment::new(rbar.to_vec(), sbar.to_vec())
}

pub fn verify_value_balance_commitment<C: CommitmentScheme, G: Group + ProjectiveCurve>(
    value_commitment: &C,
    input_value_commitments: &Vec<C::Output>,
    output_value_commitments: &Vec<C::Output>,
    value_balance: i64,
    input: &[u8],
    signature: &ValueBalanceCommitment,
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
    let c: <G as Group>::ScalarField = hash_into_field::<G>(&signature.rbar[..], input);
    let affine_r = recover_affine_from_x_coord::<G>(&signature.rbar)?;

    let zero: i64 = 0;
    let s: C::Randomness = FromBytes::read_le(&signature.sbar[..])?;
    let recommit = to_bytes_le![value_commitment.commit(&zero.to_le_bytes(), &s)?]?;
    let recovered_recommit = recover_affine_from_x_coord::<G>(&recommit).unwrap();

    let check_verification = bvk.mul(c).add(&affine_r).add(&recovered_recommit.neg());

    Ok(check_verification.is_zero())
}

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
    signature: &ValueBalanceCommitment,
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

    let c_field: <G as Group>::ScalarField = hash_into_field::<G>(&signature.rbar[..], input);
    let c: C::Randomness = FromBytes::read_le(&to_bytes_le![c_field]?[..])?;

    let affine_r = recover_affine_from_x_coord::<G>(&signature.rbar)?;

    let zero: i64 = 0;
    let s: C::Randomness = FromBytes::read_le(&signature.sbar[..])?;
    let recommit = to_bytes_le![value_commitment.commit(&zero.to_le_bytes(), &s)?]?;
    let recovered_recommit = recover_affine_from_x_coord::<G>(&recommit).unwrap();

    let partial_bvk: G = FromBytes::read_le(&to_bytes_le![partial_bvk.into_projective()]?[..])?;
    let affine_r: G = FromBytes::read_le(&to_bytes_le![affine_r.into_projective()]?[..])?;
    let recovered_recommit: G = FromBytes::read_le(&to_bytes_le![recovered_recommit.into_projective()]?[..])?;

    Ok((c, partial_bvk, affine_r, recovered_recommit))
}
