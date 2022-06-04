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

use crate::{keys::*, preprocess::*, utils::*};

use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::Zero;

use anyhow::{anyhow, Result};
use std::collections::HashMap;

/// A partial signature, made by each participant  of the (t-out-of-n) secret
/// sharing scheme where t is the threshold required to reconstruct a secret
/// from a total of n shares.
pub struct PartialThresholdSignature<G: AffineCurve> {
    /// The index of the participant.
    pub participant_index: u64,
    /// The participant's signature over the message.
    pub partial_signature: G::ScalarField,
}

impl<G: AffineCurve> PartialThresholdSignature<G> {
    /// Generate a new partial threshold signature for a participant.
    ///
    /// `participant_signing_share` - Keys required for the participant to sign.
    /// `signing_nonces` - (private) The signing nonces the participant has kept secret.
    /// `signing_commitments` - (public) The list of signing commitments published by participants.
    /// `message` - (public) The message to be signed.
    ///
    /// z_i = d_i + (e_i + rho_i) + lambda_i * (s_i + c)
    /// s_i = secret key
    /// d_i and e_i = signing nonces
    /// rho_i = binding value = H_1(i, message, signer's signing commitment)
    /// lambda_i = Lagrange coefficient
    /// c = challenge = H_2(group commitment, group public key, message)
    pub fn new(
        participant_signing_share: SignerShare<G>,
        signing_nonces: &SigningNonce<G::ScalarField>,
        signing_commitments: Vec<SigningCommitment<G>>,
        message: Vec<u8>,
    ) -> Result<Self> {
        // Calculate the binding values for each other participant.
        let mut binding_values: HashMap<u64, G::ScalarField> = HashMap::with_capacity(signing_commitments.len());
        for commitment in &signing_commitments {
            let rho_i = calculate_binding_value::<G>(commitment.participant_index, &signing_commitments, &message)?;
            binding_values.insert(commitment.participant_index, rho_i);
        }

        let signer_binding_value = binding_values
            .get(&participant_signing_share.participant_index)
            .ok_or_else(|| anyhow!("Missing binding value"))?;

        // Calculate the group commitment.
        let group_commitment = calculate_group_commitment(&signing_commitments, &binding_values)?;

        // Generate the challenge.
        let challenge = generate_challenge(&group_commitment, &participant_signing_share.group_public_key, &message)?;

        // Calculate the lagrange coefficient.
        let participant_indexes: Vec<u64> =
            signing_commitments.iter().map(|commitment| commitment.participant_index).collect();
        let lambda_i =
            calculate_lagrange_coefficients::<G>(participant_signing_share.participant_index, &participant_indexes)?;

        // Calculate the signature.
        // z_i = d_i + (e_i + rho_i) + lambda_i * (s_i + c)
        let partial_signature = signing_nonces.hiding
            + (signing_nonces.binding * signer_binding_value)
            + (lambda_i * participant_signing_share.secret_key.0 * challenge);

        Ok(Self { participant_index: participant_signing_share.participant_index, partial_signature })
    }

    /// Verify that the partial signature is valid.
    pub fn is_valid(
        &self,
        public_key: &SignerPublicKey<G>,
        challenge: G::ScalarField,
        lambda_i: G::ScalarField,
        commitment: G,
    ) -> bool {
        // Verify that g^z_i = commitment * public_key^{challenge * lambda_i}

        let expected = G::prime_subgroup_generator().mul(self.partial_signature);
        let candidate = commitment.to_projective() + public_key.0.mul(challenge * lambda_i);

        expected.eq(&candidate)
    }
}

/// A completed and aggregated threshold signature.
pub struct ThresholdSignature<G: AffineCurve> {
    pub r: G,
    pub z: G::ScalarField,
}

impl<G: AffineCurve> ThresholdSignature<G> {
    pub fn aggregate_signatures(
        partial_signatures: Vec<PartialThresholdSignature<G>>,
        signing_commitments: Vec<SigningCommitment<G>>,
        message: Vec<u8>,
        public_keys: PublicKeys<G>,
    ) -> Result<Self> {
        // Calculate the binding values for each other participant.
        let mut binding_values: HashMap<u64, G::ScalarField> = HashMap::with_capacity(signing_commitments.len());
        for commitment in &signing_commitments {
            let rho_i = calculate_binding_value::<G>(commitment.participant_index, &signing_commitments, &message)?;
            binding_values.insert(commitment.participant_index, rho_i);
        }

        // Calculate the group commitment.
        let group_commitment = calculate_group_commitment(&signing_commitments, &binding_values)?;

        // Generate the challenge.
        let challenge = generate_challenge(&group_commitment, &public_keys.group_public_key, &message)?;

        let participant_indexes: Vec<u64> =
            signing_commitments.iter().map(|commitment| commitment.participant_index).collect();

        // Check that each partial signature is valid.
        for partial_signature in &partial_signatures {
            let lambda_i =
                calculate_lagrange_coefficients::<G>(partial_signature.participant_index, &participant_indexes)?;

            let signer_public_key = public_keys
                .public_keys
                .get(&partial_signature.participant_index)
                .ok_or_else(|| anyhow!("Missing public key"))?;

            let signer_binding_value = binding_values
                .get(&partial_signature.participant_index)
                .ok_or_else(|| anyhow!("Missing binding value"))?;

            let signer_commitment = signing_commitments
                .iter()
                .find(|commitment| commitment.participant_index == partial_signature.participant_index)
                .ok_or_else(|| anyhow!("Missing signing commitment"))?;

            let commitment_i =
                signer_commitment.hiding.to_projective() + (signer_commitment.binding.mul(*signer_binding_value));

            if !partial_signature.is_valid(signer_public_key, challenge, lambda_i, commitment_i.to_affine()) {
                return Err(anyhow!("Invalid partial signature"));
            }
        }

        let mut z = G::ScalarField::zero();
        for partial_signature in &partial_signatures {
            z += partial_signature.partial_signature;
        }

        Ok(Self { r: group_commitment, z })
    }
}
