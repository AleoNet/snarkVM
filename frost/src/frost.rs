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

use crate::preprocess::*;

use snarkvm_curves::AffineCurve;
use snarkvm_fields::Field;

use rand::Rng;

/// A monolith construction of the FROST protocol.

/// The public key used to verify a threshold signature made by a group of signers.
pub struct GroupPublicKey<G: AffineCurve>(pub G);

/// The signer's secret key
pub struct SignerSecretKey<G: AffineCurve>(pub <G as AffineCurve>::ScalarField);

/// The signer's public key.
pub struct SignerPublicKey<G: AffineCurve>(pub G);

/// A FROST keypair used by participants to sign and verify.
pub struct SignerKeyPair<G: AffineCurve> {
    pub participant_index: u64,
    pub public_key: SignerPublicKey<G>,
    pub secret_key: SignerSecretKey<G>,
    pub group_public_key: GroupPublicKey<G>,
}

/// A partial signature, made by each participant  of the (t-out-of-n) secret
/// sharing scheme where t is the threshold required to reconstruct a secret
/// from a total of n shares.
pub struct PartialThresholdSignature<G: AffineCurve> {
    /// The index of the participant.
    pub participant_index: u32,
    /// The participant's signature over the message.
    pub partial_signature: <G as AffineCurve>::ScalarField,
}

impl<G: AffineCurve> PartialThresholdSignature<G> {
    /// Verify that the partial signature is valid.
    pub fn is_valid(
        &self,
        public_key: SignerPublicKey<G>,
        challenge: <G as AffineCurve>::ScalarField,
        lambda_i: <G as AffineCurve>::ScalarField,
        commitment: G,
    ) -> bool {
        // Verify that g^z_i = commitment * public_key^{challenge * lambda_i}

        let expected = G::prime_subgroup_generator().mul(self.partial_signature);
        let candidate = commitment.to_projective() + public_key.0.mul(challenge * lambda_i);

        expected.eq(&candidate)
    }
}

/// A completed and aggregated threshold signature.
pub struct ThresholdSignature<F: Field> {
    pub z: F,
}

// TODO (raychu86): Public verification share

// 1. Keygen for each signer
// 2. Each signer verify proof of knowledge of other signers
// 3. Each signer generate shares
// 4. Each signer verifies shares of other signers
// 5. Reconstruct the secret
