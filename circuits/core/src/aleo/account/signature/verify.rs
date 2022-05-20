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
        // Compute G^sk_sig^challenge.
        let pk_sig_challenge = self.compute_key.pk_sig() * &self.challenge;

        // Compute G^randomizer := G^s G^sk_sig^challenge.
        let g_randomizer = A::g_scalar_multiply(&self.response) + pk_sig_challenge;

        // Compute the candidate verifier challenge.
        let candidate_challenge = {
            // Convert the message into little-endian bits.
            let message_bits = message.to_bits_le();
            let message_elements =
                message_bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect::<Vec<_>>();

            // Construct the hash input (G^sk_sig G^r_sig G^sk_prf, G^randomizer, message).
            let mut preimage = Vec::with_capacity(3 + message_elements.len());
            preimage.push(address.to_field());
            preimage.push(g_randomizer.to_x_coordinate());
            preimage.push(Field::constant((message_bits.len() as u128).into())); // <- Message length *must* be constant.
            preimage.extend_from_slice(&message_elements);

            // Hash to derive the verifier challenge.
            A::hash_to_scalar_psd8(&preimage)
        };

        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_address = {
            // Compute G^sk_prf.
            let pk_prf = A::g_scalar_multiply(self.compute_key.sk_prf());
            // Compute G^sk_sig G^r_sig G^sk_prf.
            self.compute_key.pk_sig() + self.compute_key.pr_sig() + pk_prf
        };

        let is_challenge_valid = self.challenge.is_equal(&candidate_challenge);
        let is_address_valid = address.to_group().is_equal(&candidate_address);

        is_challenge_valid & is_address_valid
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::aleo::{account::helpers::generate_account, Devnet as Circuit};
    use snarkvm_circuits_types::Group;
    use snarkvm_console_aleo::Signature as NativeSignature;
    use snarkvm_utilities::{test_crypto_rng, test_rng, UniformRand};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for i in 0..ITERATIONS {
            // Generate a private key, compute key, view key, and address.
            let (private_key, compute_key, _view_key, address) = generate_account()?;

            // Retrieve the native compute key components.
            let pk_sig = compute_key.pk_sig();
            let pr_sig = compute_key.pr_sig();
            let pk_vrf = compute_key.pk_vrf();

            // Sample a random message.
            let rng = &mut test_rng();
            let message = vec![
                Literal::Address(Address::new(mode, UniformRand::rand(rng))),
                Literal::Boolean(Boolean::new(mode, UniformRand::rand(rng))),
                Literal::Field(Field::new(mode, UniformRand::rand(rng))),
                Literal::Group(Group::new(mode, UniformRand::rand(rng))),
                Literal::Scalar(Scalar::new(mode, UniformRand::rand(rng))),
            ];

            // Generate a signature.
            let randomizer = UniformRand::rand(&mut test_crypto_rng());
            let signature = NativeSignature::sign(&private_key, &message.to_bits_le().eject_value(), randomizer)?;

            // Retrieve the challenge and response.
            let challenge = signature.challenge();
            let response = signature.response();

            // Initialize the signature and address.
            let signature = Signature::<Circuit>::new(mode, (challenge, response, (pk_sig, pr_sig, pk_vrf)));
            let address = Address::new(mode, *address);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = signature.verify(&address, &message);
                assert!(candidate.eject_value());
                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(<=num_constants, num_public, num_private, num_constraints);
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 4325, 0, 0, 0)
    }

    #[test]
    fn test_verify_public() -> Result<()> {
        check_verify(Mode::Public, 1757, 0, 6534, 6538)
    }

    #[test]
    fn test_verify_private() -> Result<()> {
        check_verify(Mode::Private, 1757, 0, 6534, 6538)
    }
}
