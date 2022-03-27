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

impl<A: Account> Signature<A> {
    /// Returns `true` if the signature is valid for the given `address` and `message`.
    pub fn verify(&self, address: &Address<A>, message: &[Literal<A>]) -> Boolean<A> {
        // Compute G^sk_sig^c.
        let pk_sig_c = &self.pk_sig * &self.verifier_challenge;

        // Compute G^r := G^s G^sk_sig^c.
        let g_r = A::g_scalar_multiply(&self.prover_response) + pk_sig_c;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = vec![];
            preimage.push(address.to_group().to_x_coordinate());
            preimage.push(g_r.to_x_coordinate());
            preimage.push(Field::constant((message.len() as u128).into())); // <- Message length *must* be constant.
            preimage.extend_from_slice(
                &message
                    .to_bits_le()
                    .chunks(A::BaseField::size_in_data_bits())
                    .map(FromBits::from_bits_le)
                    .collect::<Vec<_>>(),
            );

            // Hash to derive the verifier challenge.
            A::hash_to_scalar(&preimage)
        };

        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_address = {
            // Compute sk_prf := RO(G^sk_sig || G^r_sig).
            let sk_prf = A::hash_to_scalar(&[self.pk_sig.to_x_coordinate(), self.pr_sig.to_x_coordinate()]);

            // Compute G^sk_prf.
            let pk_prf = A::g_scalar_multiply(&sk_prf);

            // Compute G^sk_sig G^r_sig G^sk_prf.
            &self.pk_sig + &self.pr_sig + pk_prf
        };

        let is_verifier_challenge_valid = self.verifier_challenge.is_equal(&candidate_verifier_challenge);
        let is_address_valid = address.is_equal(&candidate_address);

        is_verifier_challenge_valid & is_address_valid
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{Aleo as Circuit, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT};
    use snarkvm_algorithms::{
        signature::{AleoSignature, AleoSignatureScheme},
        SignatureScheme,
        SignatureSchemeOperations,
    };
    use snarkvm_curves::AffineCurve;
    use snarkvm_utilities::{bytes_from_bits_le, test_crypto_rng, test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    #[allow(clippy::type_complexity)]
    pub(crate) fn generate_private_key_and_address()
    -> (<Circuit as Environment>::ScalarField, <Circuit as Environment>::ScalarField, <Circuit as Environment>::Affine)
    {
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

        // Return the private key components and address.
        (sk_sig, r_sig, pk_sig + pr_sig + sk_prf)
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn generate_signature(
        (sk_sig, r_sig): (<Circuit as Environment>::ScalarField, <Circuit as Environment>::ScalarField),
        message: &[Literal<Circuit>],
    ) -> AleoSignature<<Circuit as Environment>::AffineParameters> {
        // Compute the signature parameters.
        let native = AleoSignatureScheme::<<Circuit as Environment>::AffineParameters>::setup(
            ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT,
        );

        // Return the signature.
        native
            .sign(&(sk_sig, r_sig), &bytes_from_bits_le(&message.to_bits_le().eject_value()), &mut test_crypto_rng())
            .expect("Failed to generate a signature")
    }

    fn check_verify(mode: Mode, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) {
        for i in 0..ITERATIONS {
            // Generate the private key and compute key components.
            let (sk_sig, r_sig, address) = generate_private_key_and_address();
            let signature = generate_signature((sk_sig, r_sig), &[Literal::Constant(0u8)]);

            // Initialize the private key.
            let private_key = PrivateKey::<Circuit>::new(mode, (sk_sig, r_sig));
            let address = Address::<Circuit>::new(mode, address);
            let signature = Signature::<Circuit>::new(
                mode,
                (
                    signature.prover_response,
                    signature.verifier_challenge,
                    signature.root_public_key().expect("Failed to recover").to_x_coordinate(),
                    signature.root_randomizer().expect("Failed to recover").to_x_coordinate(),
                ),
            );

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = signature.verify(&address, &message);
                assert!(candidate.eject_value());

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
