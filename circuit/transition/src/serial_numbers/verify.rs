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

impl<A: Aleo> SerialNumbers<A> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, address, function_call, ∀ \[H, r * H, gamma\])
    pub fn verify(&self, address: &Address<A>, function_call: &[Field<A>], commitments: &[Field<A>]) -> Boolean<A> {
        // Retrieve the proof components.
        let (challenge, response, compute_key, gammas) = &self.signature;

        // Retrieve pk_sig.
        let pk_sig = compute_key.pk_sig();
        // Retrieve pr_sig.
        let pr_sig = compute_key.pr_sig();
        // Compute `g_r` as `(challenge * address) + (response * G)`, equivalent to `r * G`.
        let g_r = (pk_sig * challenge) + A::g_scalar_multiply(response);

        // Construct the hash input as `(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let mut preimage = Vec::with_capacity(4 + (3 * commitments.len()) + function_call.len());
        preimage.push(A::serial_number_domain());
        preimage.extend([&g_r, pk_sig, pr_sig].map(|point| point.to_x_coordinate()));
        preimage.push(address.to_field());
        preimage.extend_from_slice(function_call);

        for ((gamma, commitment), serial_number) in gammas.into_iter().zip_eq(commitments).zip_eq(&self.serial_numbers)
        {
            // Compute the generator `H` as `HashToGroup(commitment)`.
            let h = A::hash_to_group_psd2(&[A::serial_number_domain(), commitment.clone()]);

            // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
            let h_r = (gamma * challenge) + (&h * response);

            // Compute `candidate_serial_number_nonce` as `HashToScalar(COFACTOR * gamma)`.
            let candidate_serial_number_nonce =
                A::hash_to_scalar_psd2(&[A::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);

            // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
            let candidate_serial_number = A::commit_bhp512(
                &(&A::serial_number_domain(), commitment).to_bits_le(),
                &candidate_serial_number_nonce,
            );

            // Append `(H, r * H, gamma)` to the hash input.
            preimage.extend([&h, &h_r, gamma].iter().map(|point| point.to_x_coordinate()));

            // Ensure the computed serial number match the expected serial number.
            serial_number.is_equal(&candidate_serial_number);
        }

        // Compute `candidate_challenge` as `HashToScalar(r * G, pk_sig, pr_sig, address, function_call, ∀ [H, r * H, gamma])`.
        let candidate_challenge = A::hash_to_scalar_psd8(&preimage);

        // Compute the candidate address.
        let candidate_address = compute_key.to_address();

        // Return `true` if the challenge and address are valid.
        challenge.is_equal(&candidate_challenge) & address.is_equal(&candidate_address)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 50;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            // Compute the native serial number.
            let private_key = snarkvm_console_account::PrivateKey::<<Circuit as Environment>::Network>::new(rng)?;
            let commitments = vec![Uniform::rand(rng), Uniform::rand(rng)];

            let sk_sig = private_key.sk_sig();
            let pr_sig = snarkvm_console_account::ComputeKey::try_from(&private_key)?.pr_sig();
            let address = snarkvm_console_account::Address::try_from(&private_key)?;

            let serial_numbers = console::SerialNumbers::<<Circuit as Environment>::Network>::sign(
                &sk_sig,
                &pr_sig,
                &commitments,
                &commitments,
                rng,
            )?;
            assert!(serial_numbers.verify(&address, &commitments, &commitments));

            // Inject the serial number and its arguments into circuits.
            let address = Address::<Circuit>::new(mode, address);
            let commitments: Vec<_> = Inject::new(mode, commitments);
            let serial_numbers = SerialNumbers::new(mode, serial_numbers);

            Circuit::scope(format!("SerialNumbers {i}"), || {
                let candidate = serial_numbers.verify(&address, &commitments, &commitments);
                assert!(candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_sign_and_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 27823, 0, 0, 0)
    }

    #[test]
    fn test_sign_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 19338, 0, 28053, 28101)
    }

    #[test]
    fn test_sign_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 19338, 0, 28053, 28101)
    }
}
