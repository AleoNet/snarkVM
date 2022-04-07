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

impl<A: Aleo> Signature<A> {
    /// Returns `true` if the signature is valid for the given `address` and `message`.
    pub fn verify(&self, address: &Address<A>, message: &[Literal<A>]) -> Boolean<A> {
        // Compute G^sk_sig^c.
        let pk_sig_c = &self.pk_sig * &self.verifier_challenge;

        // Compute G^r := G^s G^sk_sig^c.
        let g_r = A::g_scalar_multiply(&self.prover_response) + pk_sig_c;

        // Compute the candidate verifier challenge.
        let candidate_verifier_challenge = {
            // Convert the message into little-endian bits.
            let message_bits = message.to_bits_le();
            let message_elements =
                message_bits.chunks(A::BaseField::size_in_data_bits()).map(FromBits::from_bits_le).collect::<Vec<_>>();

            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^r, message).
            let mut preimage = Vec::with_capacity(3 + message_elements.len());
            preimage.push(address.to_group().to_x_coordinate());
            preimage.push(g_r.to_x_coordinate());
            preimage.push(Field::constant((message_bits.len() as u128).into())); // <- Message length *must* be constant.
            preimage.extend_from_slice(&message_elements);

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
        let is_address_valid = address.to_group().is_equal(&candidate_address);

        is_verifier_challenge_valid & is_address_valid
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_algorithms::{signature::AleoSignature, SignatureScheme, SignatureSchemeOperations};
    use snarkvm_curves::{AffineCurve, ProjectiveCurve};
    use snarkvm_utilities::{test_crypto_rng, test_rng, UniformRand};

    const ITERATIONS: usize = 100;

    pub type NativeAffine = <Circuit as Environment>::Affine;
    pub type NativeAffineParameters = <Circuit as Environment>::AffineParameters;
    pub type NativeScalarField = <Circuit as Environment>::ScalarField;

    pub(crate) fn generate_private_key_and_address() -> (NativeScalarField, NativeScalarField, NativeAffine) {
        // Compute the signature parameters.
        let native = Circuit::native_signature_scheme();

        // Sample a random private key.
        let rng = &mut test_rng();
        let sk_sig: NativeScalarField = UniformRand::rand(rng);
        let r_sig: NativeScalarField = UniformRand::rand(rng);

        // Compute G^sk_sig.
        let pk_sig = native.g_scalar_multiply(&sk_sig);
        // Compute G^r_sig.
        let pr_sig = native.g_scalar_multiply(&r_sig);
        // Compute sk_prf := RO(G^sk_sig || G^r_sig).
        let sk_prf =
            native.hash_to_scalar_field(&[pk_sig.to_affine().to_x_coordinate(), pr_sig.to_affine().to_x_coordinate()]);
        // Compute G^sk_prf.
        let pk_prf = native.g_scalar_multiply(&sk_prf);

        // Return the private key components and address.
        (sk_sig, r_sig, (pk_sig + pr_sig + pk_prf).into())
    }

    pub(crate) fn generate_signature(
        (sk_sig, r_sig): (&NativeScalarField, &NativeScalarField),
        address: &NativeAffine,
        message: &[Literal<Circuit>],
    ) -> AleoSignature<NativeAffineParameters> {
        let rng = &mut test_crypto_rng();
        let native = Circuit::native_signature_scheme();

        // Compute the signature.
        let message = message.to_bits_le().eject_value();
        let signature = native.sign(&(*sk_sig, *r_sig), &message, rng).expect("Failed to sign");
        assert!(native.verify(address, &message, &signature).expect("Failed to verify signature"));
        signature
    }

    fn check_verify(mode: Mode, num_constants: usize, num_public: usize, num_private: usize, num_constraints: usize) {
        for i in 0..ITERATIONS {
            let rng = &mut test_rng();

            // Sample a random message.
            let message = vec![
                Literal::Address(Address::new(mode, UniformRand::rand(rng))),
                Literal::Boolean(Boolean::new(mode, UniformRand::rand(rng))),
                Literal::Field(Field::new(mode, UniformRand::rand(rng))),
                Literal::Group(Group::new(mode, UniformRand::rand(rng))),
                Literal::Scalar(Scalar::new(mode, UniformRand::rand(rng))),
            ];

            // Generate the private key and compute key components.
            let (sk_sig, r_sig, address) = generate_private_key_and_address();
            let signature = generate_signature((&sk_sig, &r_sig), &address, &message);

            // Initialize the private key.
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
        check_verify(Mode::Constant, 4287, 0, 0, 0);
    }

    #[test]
    fn test_verify_public() {
        check_verify(Mode::Public, 1770, 0, 7325, 7330);
    }

    #[test]
    fn test_verify_private() {
        check_verify(Mode::Private, 1770, 0, 7325, 7330);
    }
}
