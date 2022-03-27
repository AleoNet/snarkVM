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

use super::*;
use crate::PrivateKey;

impl<A: Account> Signature<A> {
    /// Returns `true` if the signature is valid for the given `address` and `message`.
    pub fn verify(&self, address: &Address<A>, message: &[Literal<A>]) -> Boolean<A> {
        // Extract (sk_sig, r_sig).
        let (sk_sig, r_sig) = (private_key.sk_sig(), private_key.r_sig());

        // Compute G^sk_sig.
        let pk_sig = A::g_scalar_multiply(sk_sig);

        // Compute G^r_sig.
        let pr_sig = A::g_scalar_multiply(r_sig);

        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = A::hash_to_scalar(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate()]);



        // Recover G^sk_sig.
        let g_sk_sig = Group::from(self.pk_sig)?;

        // Compute G^sk_sig^c.
        let g_sk_sig_c = self.scalar_multiply(g_sk_sig.into_projective(), verifier_challenge);

        // Compute G^r := G^s G^sk_sig^c.
        let g_r = self.g_scalar_multiply(prover_response) + g_sk_sig_c;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = vec![];
            preimage.extend_from_slice(&public_key.x.to_field_elements()?);
            preimage.extend_from_slice(&g_r.x.to_field_elements()?);
            preimage.push(TE::BaseField::from(message.len() as u128));
            preimage.extend_from_slice(&message.to_field_elements()?);

            // Hash to derive the verifier challenge.
            self.hash_to_scalar_field(&preimage)
        };

        // Recover G^r_sig.
        let g_r_sig = Self::recover_from_x_coordinate(root_randomizer)?;

        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_public_key = {
            // Compute sk_prf := RO(G^sk_sig || G^r_sig).
            let sk_prf = self.hash_to_scalar_field(&[g_sk_sig.x, g_r_sig.x]);

            // Compute G^sk_prf.
            let g_sk_prf = self.g_scalar_multiply(&sk_prf);

            // Compute G^sk_sig G^r_sig G^sk_prf.
            g_sk_sig + g_r_sig + g_sk_prf
        };

        Ok(*verifier_challenge == candidate_verifier_challenge && *public_key == candidate_public_key)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{Aleo as Circuit, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT};
    use snarkvm_algorithms::{signature::AleoSignatureScheme, SignatureScheme, SignatureSchemeOperations};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    #[allow(clippy::type_complexity)]
    pub(crate) fn generate_private_and_compute_key() -> (
        <Circuit as Environment>::ScalarField,
        <Circuit as Environment>::ScalarField,
        <Circuit as Environment>::Affine,
        <Circuit as Environment>::Affine,
        <Circuit as Environment>::ScalarField,
    ) {
        // Compute the signature parameters.
        let native = AleoSignatureScheme::<<Circuit as Environment>::AffineParameters>::setup(
            ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT,
        );

        // Sample a random private key.
        let rng = &mut test_rng();
        let sk_sig: <Circuit as Environment>::ScalarField = UniformRand::rand(rng);
        let r_sig: <Circuit as Environment>::ScalarField = UniformRand::rand(rng);

        // Compute G^sk_sig.
        let pk_sig = native.g_scalar_multiply(&sk_sig);
        // Compute G^r_sig.
        let pr_sig = native.g_scalar_multiply(&r_sig);
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf = native.hash_to_scalar_field(&[pk_sig.x, pr_sig.x]);

        // Return the private key and compute key components.
        (sk_sig, r_sig, pk_sig, pr_sig, sk_prf)
    }

    fn check_verify(mode: Mode, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) {
        for i in 0..ITERATIONS {
            // Generate the private key and compute key components.
            let (sk_sig, r_sig, pk_sig, pr_sig, sk_prf) = generate_private_and_compute_key();

            // Initialize the private key.
            let private_key = PrivateKey::<Circuit>::new(mode, (sk_sig, r_sig));

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = ComputeKey::verify(&private_key);
                assert_eq!(pk_sig, candidate.pk_sig().eject_value());
                assert_eq!(pr_sig, candidate.pr_sig().eject_value());
                assert_eq!(sk_prf, candidate.sk_prf().eject_value());

                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(num_constants, num_public, num_private, num_constraints);
                }
            });
        }
    }

    #[test]
    fn test_verify_constant() {
        check_verify(Mode::Constant, 2261, 0, 0, 0);
    }

    #[test]
    fn test_verify_public() {
        check_verify(Mode::Public, 1008, 0, 3093, 3094);
    }

    #[test]
    fn test_verify_private() {
        check_verify(Mode::Private, 1008, 0, 3093, 3094);
    }
}
