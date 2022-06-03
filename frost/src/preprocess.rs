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

use snarkvm_curves::AffineCurve;
use snarkvm_fields::Field;

use rand::Rng;

/// The hiding and binding nonces used (only once) for a signing operation.
pub struct SigningNonce<F: Field> {
    /// d\_{ij}
    hiding: F,
    /// e\_{ij}
    binding: F,
}

impl<F: Field> SigningNonce<F> {
    pub fn new<R: Rng>(rng: &mut R) -> Self {
        Self { hiding: F::rand(rng), binding: F::rand(rng) }
    }
}

/// A precomputed commitment share.
pub struct CommitmentShare<G: AffineCurve> {
    /// The index of the participant.
    pub participant_index: u64,
    /// The hiding commitment - D\_{ij}.
    pub hiding: G,
    /// The binding commitment - E\_{ij}.
    pub binding: G,
}

impl<G: AffineCurve> CommitmentShare<G> {
    /// Generate the commitment share for a given participant index using a provided nonce.
    pub fn from(participant_index: u64, nonce: &SigningNonce<<G as AffineCurve>::ScalarField>) -> Self {
        // TODO (raychu86): Confirm that the basepoint selection is correct.
        let basepoint = G::prime_subgroup_generator();

        Self {
            participant_index,
            hiding: basepoint.mul(nonce.hiding).into(),
            binding: basepoint.mul(nonce.binding).into(),
        }
    }
}

/// Performs the precomputation of nonces and commitments used by each participant during signing.
///
/// Every participant must call this function before signing. In the case of a two-round FROST protocol,
/// then `num_nonces` should be set to 1.
///
/// SigningNonce should be kept secret, while CommitmentShare should be distributed to other participants.
///
pub fn preprocess<G: AffineCurve, R: Rng>(
    num_nonces: usize,
    participant_index: u64,
    rng: &mut R,
) -> (Vec<SigningNonce<<G as AffineCurve>::ScalarField>>, Vec<CommitmentShare<G>>) {
    let mut singing_nonces = Vec::with_capacity(num_nonces);
    let mut commitment_shares = Vec::with_capacity(num_nonces);

    for _ in 0..num_nonces {
        let nonce = SigningNonce::new(rng);
        let share = CommitmentShare::from(participant_index, &nonce);
        singing_nonces.push(nonce);
        commitment_shares.push(share);
    }

    (singing_nonces, commitment_shares)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_nonce_into_commitment_share() {}

    #[test]
    fn test_preprocess() {}
}
