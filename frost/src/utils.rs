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

use crate::{preprocess::SigningCommitment, GroupPublicKey};

use console::algorithms::{Hash, HashToScalar, Poseidon4};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::{Field, One, PrimeField, ToConstraintField, Zero};

use anyhow::{anyhow, Result};
use std::{
    collections::HashMap,
    ops::{Mul, Sub},
};

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

/// Generates the binding value, `rho_i` that ensures the signature is unique for a particular
/// signing set, set of commitments, and message.
pub fn calculate_binding_value<G: AffineCurve>(
    participant_index: u64,
    signing_commitments: &[SigningCommitment<G>],
    message: &[u8],
) -> Result<G::ScalarField>
where
    G::BaseField: PrimeField,
{
    // TODO (raychu86): Move this setup out of the function.
    let poseidon4 = Poseidon4::<G::BaseField>::setup("FROST_binding_value")?;

    let message_hash = poseidon4.hash(&message.to_field_elements()?)?;

    let mut preimage = Vec::new();
    preimage.extend(&"FROST_SHA256".as_bytes().to_field_elements()?);
    preimage.push(
        G::BaseField::from_repr(participant_index.into())
            .ok_or_else(|| anyhow!("Failed to convert participant index to scalar"))?,
    );
    preimage.push(message_hash);

    for commitment in signing_commitments {
        preimage.push(
            G::BaseField::from_repr(commitment.participant_index.into())
                .ok_or_else(|| anyhow!("Failed to convert participant index to scalar"))?,
        );
        preimage.push(commitment.hiding.to_x_coordinate());
        preimage.push(commitment.binding.to_x_coordinate());
    }

    poseidon4.hash_to_scalar(&preimage[..])
}

/// Calculate the group commitment which is published as part of the joint
/// Schnorr signature.
pub fn calculate_group_commitment<G: AffineCurve>(
    signing_commitments: &[SigningCommitment<G>],
    binding_values: &HashMap<u64, G::ScalarField>,
) -> Result<G> {
    let mut accumulator = G::zero().to_projective();

    for commitment in signing_commitments.iter() {
        // Enforce that the signing commitments won't reveal the signer's
        if G::zero() == commitment.binding || G::zero() == commitment.hiding {
            return Err(anyhow!("Commitment equals the identity."));
        }

        let rho_i =
            binding_values.get(&commitment.participant_index).ok_or_else(|| anyhow!("No matching commitment index"))?;
        accumulator += commitment.hiding.to_projective() + (commitment.binding.mul(*rho_i))
    }

    Ok(accumulator.to_affine())
}

/// Generate the challenge required for Schnorr signatures.
pub fn generate_challenge<G: AffineCurve>(
    group_commitment: &G,
    group_public_key: &GroupPublicKey<G>,
    message: &[u8],
) -> Result<G::ScalarField>
where
    G::BaseField: PrimeField,
{
    // TODO (raychu86): Move this setup out of the function.
    let poseidon4 = Poseidon4::<G::BaseField>::setup("FROST_challenge")?;

    let mut preimage = vec![];
    preimage.push(group_commitment.to_x_coordinate());
    preimage.push(group_public_key.0.to_x_coordinate());
    preimage.push(G::BaseField::from(message.len() as u128));
    preimage.extend(&message.to_field_elements()?);

    poseidon4.hash_to_scalar(&preimage[..])
}
