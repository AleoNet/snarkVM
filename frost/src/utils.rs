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

use crate::preprocess::SigningCommitment;

use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{Field, One, PrimeField, Zero};

use crate::GroupPublicKey;
use anyhow::{anyhow, Result};
use sha2::{Digest, Sha256};
use snarkvm_utilities::ToBytes;
use std::{
    collections::HashMap,
    ops::{Mul, Sub},
};

pub fn sha256(data: &[u8]) -> [u8; 32] {
    let digest = Sha256::digest(&data);
    let mut ret = [0u8; 32];
    ret.copy_from_slice(&digest);
    ret
}

/// Calculate the Lagrange coefficient for a given participant index.
pub fn calculate_lagrange_coefficients<G: AffineCurve>(
    participant_index: u64,
    all_participant_indices: &[u64],
) -> Result<G::ScalarField> {
    let mut numerator = G::ScalarField::one();
    let mut denominator = G::ScalarField::one();

    let participant_index_scalar = match G::ScalarField::from_repr(participant_index.into()) {
        Some(scalar) => scalar,
        None => Err(anyhow!("Failed to convert participant index to scalar"))?,
    };

    for index in all_participant_indices {
        // Skip the index if it is the same as the participant index.
        if index == &participant_index {
            continue;
        }

        let scalar = match G::ScalarField::from_repr((*index).into()) {
            Some(res) => res,
            None => return Err(anyhow!("Failed to convert index to scalar")),
        };

        numerator = numerator.mul(scalar);
        denominator = denominator.mul(scalar.sub(participant_index_scalar));
    }

    if denominator == G::ScalarField::zero() {
        return Err(anyhow!("There was a duplicate index"));
    }

    let inverted_denominator = match denominator.inverse() {
        Some(res) => res,
        None => return Err(anyhow!("Failed to invert denominator")),
    };

    Ok(numerator.mul(inverted_denominator))
}

// TODO (raychu86): Use hash_to_scalar_field instead of sha256.
/// Generates the binding value, `rho_i` that ensures the signature is unique for a particular
/// signing set, set of commitments, and message.
pub fn calculate_binding_value<G: AffineCurve>(
    participant_index: u64,
    signing_commitments: &[SigningCommitment<G>],
    message: &[u8],
) -> Result<G::ScalarField> {
    let message_hash = sha256(message);

    let mut hash_input = ["FROST_SHA256".as_bytes(), &participant_index.to_bytes_le()?, &message_hash].concat();

    for commitment in signing_commitments {
        hash_input.extend(commitment.participant_index.to_bytes_le()?);
        hash_input.extend(commitment.hiding.to_x_coordinate().to_bytes_le()?);
        hash_input.extend(commitment.binding.to_x_coordinate().to_bytes_le()?);
    }

    let result = sha256(&hash_input);

    match G::ScalarField::from_random_bytes(&result) {
        Some(res) => Ok(res),
        None => Err(anyhow!("Failed to convert result to scalar")),
    }
}

/// Calculate the group commitment which is published as part of the joint
/// Schnorr signature.
pub fn calculate_group_commitment<G: AffineCurve>(
    signing_commitments: &[SigningCommitment<G>],
    binding_values: &HashMap<u64, G::ScalarField>,
) -> Result<G> {
    let mut accumulator = G::zero().to_projective();

    for commitment in signing_commitments.iter() {
        // The following check prevents a party from accidentally revealing their share.
        // Note that the '&&' operator would be sufficient.
        if G::zero() == commitment.binding || G::zero() == commitment.hiding {
            return Err(anyhow!("Commitment equals the identity."));
        }

        let rho_i = binding_values.get(&commitment.participant_index).ok_or(anyhow!("No matching commitment index"))?;
        accumulator += commitment.hiding.to_projective() + (commitment.binding.mul(*rho_i))
    }

    Ok(accumulator.to_affine())
}

/// Generate the challenge required for Schnorr signatures.
pub fn generate_challenge<G: AffineCurve>(
    group_commitment: &G,
    group_public_key: &GroupPublicKey<G>,
    message: &[u8],
) -> Result<G::ScalarField> {
    let hash_input =
        [group_commitment.to_x_coordinate().to_bytes_le()?, group_public_key.0.to_bytes_le()?, message.to_vec()]
            .concat();

    let result = sha256(&hash_input);

    match G::ScalarField::from_random_bytes(&result) {
        Some(res) => Ok(res),
        None => Err(anyhow!("Failed to convert result to scalar")),
    }
}
