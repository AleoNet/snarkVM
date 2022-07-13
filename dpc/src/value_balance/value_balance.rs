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

use crate::{error::ValueBalanceCommitmentError, AleoAmount, Network};
use snarkvm_algorithms::CommitmentScheme;
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{ConstraintFieldError, PrimeField, ToConstraintField, Zero};
use snarkvm_utilities::{FromBytes, ToBytes};

use blake2::{
    digest::{Update, VariableOutput},
    Blake2bVar,
};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::{
    io::{Read, Result as IoResult, Write},
    ops::{Add, Mul, Neg},
};

/// Returns a scalar field derived from a hashed input.
pub fn hash_to_scalar<N: Network>(a: &[u8], b: &[u8]) -> N::ProgramScalarField {
    let mut hasher = Blake2bVar::new(64).unwrap();
    hasher.update(a);
    hasher.update(b);

    let mut hash = [0u8; 64];
    hasher.finalize_variable(&mut hash).unwrap();

    N::ProgramScalarField::from_bytes_le_mod_order(&hash)
}

///
/// The value balance commitment scheme used to enforce value conservation.
/// Derived from the Zcash binding signature scheme - https://github.com/zcash/zips/blob/main/protocol/protocol.pdf
///
/// The scheme relies on the homomorphic properties of the commitment scheme
/// to enforce that the attributes of `ValueBalanceCommitment` can hold the following:
///
/// vb = value_balance
/// combined_randomness = signing key = input_value_commitment_randomness - output_value_commitment_randomness
/// combined_commitments = validating key = (input_value_commitments - output_value_commitments) - commitment(vb, 0)
/// vb_c = value balance commitment
/// vb_c.derive_public(combined_randomness) = combined_commitments
///
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
pub struct ValueBalanceCommitment<N: Network> {
    /// Commitment = Commit(0, Hash( rng || message)).
    pub commitment: N::ValueCommitment,
    /// Blinding factor = `randomness` * `combined_randomness` + Hash( rng || message).
    pub blinding_factor: N::ProgramScalarField,
}

impl<N: Network> ValueBalanceCommitment<N> {
    ///
    /// Returns the value balance commitment given:
    ///  - `input_value_commitments` are the commitments on the input record values,
    ///  - `output_value_commitments` are the commitments on the output record values,
    ///  - `input_value_commitment_randomness` are the random scalars used for the `input_value_commitments`,
    ///  - `output_value_commitment_randomness` are the random scalars used for the `output_value_commitments`,
    ///  - `value_balance` is the final balance (total input values - total output values),
    ///  - `input` is the message that is being signed. i.e. a checkpoint, transition id, etc,
    ///  - `rng` is the randomness used to generate the final commitment.
    ///
    pub fn new<R: Rng>(
        input_value_commitments: &[N::ValueCommitment],
        output_value_commitments: &[N::ValueCommitment],
        input_value_commitment_randomness: &[N::ProgramScalarField],
        output_value_commitment_randomness: &[N::ProgramScalarField],
        value_balance: AleoAmount,
        input: &[u8],
        rng: &mut R,
    ) -> Result<ValueBalanceCommitment<N>, ValueBalanceCommitmentError> {
        // Calculate the `combined_randomness`.
        let mut combined_randomness = N::ProgramScalarField::zero();

        for input_vc_randomness in input_value_commitment_randomness {
            combined_randomness += input_vc_randomness;
        }

        for output_vc_randomness in output_value_commitment_randomness {
            combined_randomness -= output_vc_randomness;
        }

        {
            // Calculate the `combined_commitments`.
            let mut combined_commitments = N::ProgramAffineCurve::zero().to_projective();

            for vc_input in input_value_commitments {
                combined_commitments.add_assign_mixed(&**vc_input);
            }

            for vc_output in output_value_commitments {
                combined_commitments.sub_assign_mixed(&**vc_output);
            }

            combined_commitments.sub_assign_mixed(&Self::commit_without_randomness(value_balance)?);

            // Make sure bvk can be derived from the cumulative randomness.
            let expected_combined_commitments =
                N::value_commitment_scheme().commit_bytes(&0i64.to_le_bytes(), &combined_randomness)?;
            assert_eq!(combined_commitments, expected_combined_commitments);
        }

        // Generate final commitment randomness.
        let mut sig_rand = [0u8; 80];
        rng.fill(&mut sig_rand[..]);

        // Construct `c` to use as randomness.
        let c = hash_to_scalar::<N>(&sig_rand[..], input);

        // Commit to 0 with `c`as randomness.
        let commitment = N::value_commitment_scheme().commit_bytes(&0i64.to_le_bytes(), &c)?;

        let mut blinding_factor = hash_to_scalar::<N>(&commitment.to_x_coordinate().to_bytes_le()?, input);
        blinding_factor = blinding_factor.mul(&combined_randomness);
        blinding_factor = blinding_factor.add(&c);

        Ok(ValueBalanceCommitment { commitment: commitment.into(), blinding_factor })
    }

    /// Returns `true` if the value balance commitment is valid.
    pub fn verify(
        &self,
        input_value_commitments: &Vec<N::ValueCommitment>,
        output_value_commitments: &Vec<N::ValueCommitment>,
        value_balance: AleoAmount,
        input: &[u8],
    ) -> Result<bool, ValueBalanceCommitmentError> {
        // Craft the combined value commitments (verifying key).
        let mut combined_commitments = N::ProgramAffineCurve::zero().to_projective();

        for vc_input in input_value_commitments {
            combined_commitments.add_assign_mixed(&**vc_input);
        }

        for vc_output in output_value_commitments {
            combined_commitments.sub_assign_mixed(&**vc_output);
        }

        combined_commitments.sub_assign_mixed(&Self::commit_without_randomness(value_balance)?);

        let c = hash_to_scalar::<N>(&self.commitment.to_x_coordinate().to_bytes_le()?, input);

        let recommit = N::value_commitment_scheme().commit_bytes(&0i64.to_le_bytes(), &self.blinding_factor)?;

        Ok((combined_commitments.mul(c) + self.commitment.to_projective() - recommit.to_projective()).is_zero())
    }

    /// Returns a commitment on the value balance with a randomness of zero.
    /// `value_balance.sign() * Commit(value.abs(), 0)`.
    fn commit_without_randomness(value: AleoAmount) -> Result<N::ProgramAffineCurve, ValueBalanceCommitmentError> {
        // Convert the value balance to an absolute u64.
        let value_as_u64 = match value.0.checked_abs() {
            Some(val) => val as u64,
            None => return Err(ValueBalanceCommitmentError::OutOfBounds(value.0)),
        };

        // Compute commitment of the value with a zero randomness.
        let zero_randomness = Zero::zero();
        let commitment = N::value_commitment_scheme().commit_bytes(&value_as_u64.to_le_bytes(), &zero_randomness)?;

        match value.is_negative() {
            true => Ok(commitment.neg()),
            false => Ok(commitment),
        }
    }

    ///
    /// Returns the broken down components used for gadget verification.
    ///
    /// `c` - The hash of `commitment` || input
    /// `partial_combined_commitments` - The combined value commitments excluding the value balance
    /// `commitment` - Commit(0, Hash( rng || message)).
    /// `blinded_commitment` - Commit(0, `blinding_factor`)
    ///
    pub fn gadget_verification_setup(
        &self,
        input_value_commitments: &[N::ValueCommitment],
        output_value_commitments: &[N::ValueCommitment],
        input: &[u8],
    ) -> Result<
        (N::ProgramScalarField, N::ProgramAffineCurve, N::ValueCommitment, N::ProgramAffineCurve),
        ValueBalanceCommitmentError,
    > {
        // Craft the partial combined value commitments (partial verifying key).
        let mut partial_combined_commitments = N::ProgramAffineCurve::zero().to_projective();

        for vc_input in input_value_commitments {
            partial_combined_commitments.add_assign_mixed(&**vc_input);
        }

        for vc_output in output_value_commitments {
            partial_combined_commitments.sub_assign_mixed(&**vc_output);
        }

        let c = hash_to_scalar::<N>(&self.commitment.to_x_coordinate().to_bytes_le()?, input);
        let blinded_commitment =
            N::value_commitment_scheme().commit_bytes(&0i64.to_le_bytes(), &self.blinding_factor)?;

        Ok((c, partial_combined_commitments.into(), self.commitment.clone(), blinded_commitment))
    }
}

impl<N: Network> Default for ValueBalanceCommitment<N> {
    fn default() -> Self {
        let commitment: N::ProgramAffineCurve = Default::default();
        Self { commitment: commitment.into(), blinding_factor: Default::default() }
    }
}

impl<N: Network> ToBytes for ValueBalanceCommitment<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.commitment.to_x_coordinate().write_le(&mut writer)?;
        self.blinding_factor.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for ValueBalanceCommitment<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x_coordinate = <N::ProgramAffineCurve as AffineCurve>::BaseField::read_le(&mut reader)?;

        if let Some(commitment) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, false) {
            if commitment.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self { commitment: commitment.into(), blinding_factor: FromBytes::read_le(&mut reader)? });
            }
        }

        if let Some(commitment) = N::ProgramAffineCurve::from_x_coordinate(x_coordinate, true) {
            if commitment.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self { commitment: commitment.into(), blinding_factor: FromBytes::read_le(&mut reader)? });
            }
        }

        Err(ValueBalanceCommitmentError::NotInCorrectSubgroupOnCurve.into())
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for ValueBalanceCommitment<N> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let commitment_fe = self.commitment.to_field_elements()?;
        let blinding_factor_fe = self.blinding_factor.to_bytes_le()?.to_field_elements()?;

        let mut field_elements = vec![];
        field_elements.extend_from_slice(&commitment_fe);
        field_elements.extend_from_slice(&blinding_factor_fe);

        Ok(field_elements)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::testnet2::Testnet2;
    use snarkvm_algorithms::CommitmentScheme;
    use snarkvm_utilities::{FromBytes, ToBytes, Uniform};

    use rand::Rng;

    pub(crate) fn generate_random_value_balance_commitment<N: Network, R: Rng>(
        input_amounts: Vec<AleoAmount>,
        output_amounts: Vec<AleoAmount>,
        sighash: &[u8],
        rng: &mut R,
    ) -> (Vec<N::ValueCommitment>, Vec<N::ValueCommitment>, AleoAmount, ValueBalanceCommitment<N>) {
        let mut value_balance = AleoAmount::ZERO;

        let mut input_value_commitment_randomness = vec![];
        let mut input_value_commitments = vec![];

        let mut output_value_commitment_randomness = vec![];
        let mut output_value_commitments = vec![];

        for input_amount in input_amounts {
            value_balance = value_balance.add(input_amount);

            let value_commit_randomness = Uniform::rand(rng);
            let value_commitment = N::value_commitment_scheme()
                .commit_bytes(&input_amount.to_bytes_le().unwrap(), &value_commit_randomness)
                .unwrap();

            input_value_commitment_randomness.push(value_commit_randomness);
            input_value_commitments.push(value_commitment.into());
        }

        for output_amount in output_amounts {
            value_balance = value_balance.sub(output_amount);

            let value_commit_randomness = Uniform::rand(rng);
            let value_commitment = N::value_commitment_scheme()
                .commit_bytes(&output_amount.to_bytes_le().unwrap(), &value_commit_randomness)
                .unwrap();

            output_value_commitment_randomness.push(value_commit_randomness);
            output_value_commitments.push(value_commitment.into());
        }

        let value_balance_commitment = ValueBalanceCommitment::<N>::new(
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

        let input_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let input_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
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
            value_balance_commitment
                .verify(&input_value_commitments, &output_value_commitments, value_balance, &sighash,)
                .unwrap()
        );
    }

    #[test]
    fn test_value_balance_commitment_serialization() {
        let rng = &mut rand::thread_rng();

        let input_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let input_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount = AleoAmount::from_gate(rng.gen_range(0..100000000));
        let output_amount_2 = AleoAmount::from_gate(rng.gen_range(0..100000000));
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
