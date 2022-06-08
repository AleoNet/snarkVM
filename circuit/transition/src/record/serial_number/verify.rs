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

impl<A: Aleo> SerialNumber<A> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_number == serial_number') where:
    ///     challenge' := HashToScalar(H, r * H, gamma, r * G, pk_sig, pr_sig, address, message)
    pub fn verify(&self, address: &Address<A>, message: &[Field<A>], commitment: &Field<A>) -> Boolean<A> {
        // Retrieve the proof components.
        let (challenge, response, compute_key, gamma) = &self.signature;
        // Retrieve pk_sig.
        let pk_sig = compute_key.pk_sig();
        // Retrieve pr_sig.
        let pr_sig = compute_key.pr_sig();

        // Compute the generator `H` as `HashToGroup(commitment)`.
        let h = A::hash_to_group_psd2(&[A::serial_number_domain(), commitment.clone()]);

        // Compute `g_r` as `(challenge * address) + (response * G)`, equivalent to `r * G`.
        let g_r = (pk_sig * challenge) + A::g_scalar_multiply(response);

        // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
        let h_r = (gamma * challenge) + (&h * response);

        // Construct the hash input as (H, H^r, gamma, G^r, pk_sig, pr_sig, address, message).
        let mut preimage = Vec::with_capacity(8 + message.len());
        preimage.push(A::serial_number_domain());
        preimage.extend([&h, &h_r, gamma, &g_r, pk_sig, pr_sig].map(|point| point.to_x_coordinate()));
        preimage.push(address.to_field());
        preimage.extend_from_slice(message);

        // Compute `candidate_challenge` as `HashToScalar(H, r * H, gamma, r * G, pk_sig, pr_sig, address, message)`.
        let candidate_challenge = A::hash_to_scalar_psd8(&preimage);

        // Compute the candidate address.
        let candidate_address = compute_key.to_address();

        // Compute `candidate_serial_number_nonce` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_serial_number_nonce =
            A::hash_to_scalar_psd2(&[A::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);

        // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
        let candidate_serial_number =
            A::commit_bhp512(&(&A::serial_number_domain(), commitment).to_bits_le(), &candidate_serial_number_nonce);

        // Return `true` if the challenge, address, and serial number are valid.
        challenge.is_equal(&candidate_challenge)
            & address.is_equal(&candidate_address)
            & self.serial_number.is_equal(&candidate_serial_number)
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
            let message = Uniform::rand(rng);
            let commitment = Uniform::rand(rng);

            let sk_sig = private_key.sk_sig();
            let pr_sig = snarkvm_console_account::ComputeKey::try_from(&private_key)?.pr_sig();
            let address = snarkvm_console_account::Address::try_from(&private_key)?;

            let serial_number = console::SerialNumber::<<Circuit as Environment>::Network>::sign(
                &sk_sig,
                &pr_sig,
                &[message],
                commitment,
                rng,
            )?;
            assert!(serial_number.verify(&address, &[message], commitment));

            // Inject the serial number and its arguments into circuits.
            let address = Address::<Circuit>::new(mode, address);
            let message = Field::new(mode, message);
            let commitment = Field::new(mode, commitment);
            let serial_number = SerialNumber::new(mode, serial_number);

            Circuit::scope(format!("SerialNumber {i}"), || {
                let candidate = serial_number.verify(&address, &[message], &commitment);
                assert!(candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_sign_and_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 20969, 0, 0, 0)
    }

    #[test]
    fn test_sign_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 15792, 0, 17301, 17326)
    }

    #[test]
    fn test_sign_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 15792, 0, 17301, 17326)
    }
}
