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
use snarkvm_fields::{PrimeField, Zero};

use anyhow::{anyhow, Result};
use std::collections::HashMap;

/// A partial signature, made by each participant  of the (t-out-of-n) secret
/// sharing scheme where t is the threshold required to reconstruct a secret
/// from a total of n shares.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialThresholdSignature<G: AffineCurve>
where
    G::BaseField: PrimeField,
{
    /// The index of the participant.
    pub participant_index: u64,
    /// The participant's signature over the message.
    pub partial_signature: G::ScalarField,
}

impl<G: AffineCurve> PartialThresholdSignature<G>
where
    G::BaseField: PrimeField,
{
    /// Generate a new partial threshold signature for a participant.
    ///
    /// `participant_signing_share` - Keys required for the participant to craft a signature.
    /// `signing_nonce` - (private) The signing nonce the participant has kept secret.
    /// `signing_commitments` - (public) Each participant's public signing commitment.
    /// `message` - (public) The message to be signed.
    ///
    /// z_i = d_i + (e_i * rho_i) + lambda_i * s_i * c
    /// s_i = secret key
    /// (d_i, e_i) = signing nonces
    /// (G^d_i, G^e_i) = (D_i, E_i) = signing commitments
    /// rho_i = binding value = H_1(i, message, signer's signing commitment)
    /// lambda_i = Lagrange coefficient
    /// c = challenge = H_2(group commitment, group public key, message)
    pub fn new(
        participant_signing_share: SignerShare<G>,
        signing_nonce: &SigningNonce<G::ScalarField>,
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
        // z_i = d_i + (e_i * rho_i) + lambda_i * s_i * c
        let partial_signature = signing_nonce.hiding
            + (signing_nonce.binding * signer_binding_value)
            + (lambda_i * participant_signing_share.secret_key.0 * challenge);

        Ok(Self { participant_index: participant_signing_share.participant_index, partial_signature })
    }

    /// Returns `true` if the partial signature is valid.
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

/// A completed and aggregated threshold signature. This is indistinguishable from a Schnorr signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdSignature<G: AffineCurve>
where
    G::BaseField: PrimeField,
{
    // The public group commitment for this signing round.
    pub group_commitment: G,
    // The aggregated threshold signature.
    pub signature: G::ScalarField,
}

impl<G: AffineCurve> ThresholdSignature<G>
where
    G::BaseField: PrimeField,
{
    /// Aggregate the partial signatures into the final signature.
    pub fn aggregate_signatures(
        partial_signatures: Vec<PartialThresholdSignature<G>>,
        signing_commitments: Vec<SigningCommitment<G>>,
        message: Vec<u8>,
        public_keys: &PublicKeys<G>,
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

        // Aggregate the partial signatures.
        let mut signature = G::ScalarField::zero();
        for partial_signature in &partial_signatures {
            signature += partial_signature.partial_signature;
        }

        Ok(Self { group_commitment, signature })
    }

    /// Returns `true` if the aggregated signature is valid.
    pub fn verify(&self, group_public_key: &GroupPublicKey<G>, message: Vec<u8>) -> Result<bool> {
        let expected_challenge = generate_challenge(&self.group_commitment, group_public_key, &message)?;
        let result = group_public_key.0.mul(-expected_challenge) + G::prime_subgroup_generator().mul(self.signature);

        Ok(result == self.group_commitment)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use snarkvm_curves::edwards_bls12::EdwardsAffine as EdwardsBls12Affine;
    use snarkvm_utilities::{test_rng, UniformRand};

    fn test_signature_verification(
        threshold: u8,
        num_participants: u8,
        message: &str,
        num_rounds: usize,
        insufficient_threshold: bool,
    ) {
        let mut rng = test_rng();
        let message = message.as_bytes().to_vec();

        // Sample the `secret`where g^`secret` = GroupPublicKey.
        let secret = <EdwardsBls12Affine as AffineCurve>::ScalarField::rand(&mut rng);

        // Generate the signer keys.
        let (shares, public_keys) =
            trusted_keygen::<_, EdwardsBls12Affine>(num_participants, threshold, &secret, &mut rng);

        let mut nonces = HashMap::with_capacity(threshold as usize);
        let mut commitments = Vec::with_capacity(threshold as usize);

        // Generate nonces and signing commitments for each participant.
        for participant_index in 1..(threshold + 1) {
            let (nonce, commitment) =
                preprocess::<EdwardsBls12Affine, _>(num_rounds, participant_index as u64, &mut rng);
            nonces.insert(participant_index as u64, nonce);
            commitments.push(commitment);
        }

        // Perform the signing and verification for each round

        for round_number in 0..num_rounds {
            let mut commitments_used_for_signing: Vec<_> =
                commitments.iter().map(|commitments| commitments[round_number].clone()).collect();

            // Craft the partial signatures for each signer
            let mut partial_signatures = Vec::with_capacity(num_participants as usize);
            for (index, nonce) in &nonces {
                let signer_share = shares.iter().find(|share| share.participant_index == *index).unwrap();

                let partial_signature = PartialThresholdSignature::new(
                    signer_share.clone(),
                    &nonce[round_number],
                    commitments_used_for_signing.clone(),
                    message.clone(),
                )
                .unwrap();

                partial_signatures.push(partial_signature);
            }

            // Attempt to aggregate the signature with `threshold - 1` signatures.
            if insufficient_threshold {
                let removed = partial_signatures.pop().unwrap();
                commitments_used_for_signing.retain(|x| x.participant_index != removed.participant_index);
            }

            // Aggregate the partial signatures.
            let aggregated_signature = ThresholdSignature::aggregate_signatures(
                partial_signatures,
                commitments_used_for_signing,
                message.clone(),
                &public_keys,
            )
            .unwrap();

            // Verify the signature.
            assert!(aggregated_signature.verify(&public_keys.group_public_key, message.clone()).unwrap());
        }
    }

    #[test]
    fn test_1_out_of_1_frost_signing_and_verification() {
        test_signature_verification(1, 1, "Message to sign", 3, false);
    }

    #[test]
    fn test_3_out_of_5_frost_signing_and_verification() {
        test_signature_verification(3, 5, "Message to sign", 3, false);
    }

    #[test]
    fn test_6_out_of_10_frost_signing_and_verification() {
        test_signature_verification(6, 10, "Message to sign", 3, false);
    }

    #[should_panic]
    #[test]
    fn test_3_out_of_5_frost_signing_and_verification_insufficient_threshold() {
        test_signature_verification(3, 5, "Message to sign", 1, true);
    }

    #[should_panic]
    #[test]
    fn test_6_out_of_10_frost_signing_and_verification_insufficient_threshold() {
        test_signature_verification(6, 10, "Message to sign", 1, true);
    }
}
