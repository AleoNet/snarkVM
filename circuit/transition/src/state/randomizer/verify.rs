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

impl<A: Aleo> Randomizer<A> {
    /// Returns `true` if the proof is valid, and `false` otherwise.
    pub fn verify(&self, address: &Address<A>, serial_numbers_digest: &Field<A>, output_index: &U16<A>) -> Boolean<A> {
        // Retrieve the proof components.
        let (gamma, challenge, response) = &self.proof;

        // Compute the generator `H` as `HashToGroup([ Hash(serial_numbers) || output_index ])`.
        let generator_h =
            A::hash_to_group_psd4(&[A::randomizer_domain(), serial_numbers_digest.clone(), output_index.to_field()]);

        // Compute `u` as `(challenge * address) + (response * G)`, equivalent to `nonce * G`.
        let u = (address.to_group() * challenge) + A::g_scalar_multiply(response);

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `nonce * H`.
        let v = (gamma * challenge) + (generator_h * response);

        // Compute `candidate_challenge` as `HashToScalar(address, gamma, nonce * G, nonce * H)`.
        let candidate_challenge =
            A::hash_to_scalar_psd4(&[&address.to_group(), gamma, &u, &v].map(|c| c.to_x_coordinate()));

        // Compute `candidate_randomizer` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_randomizer =
            A::hash_to_scalar_psd2(&[A::randomizer_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);

        // Return `true` the challenge and randomizer is valid.
        challenge.is_equal(&candidate_challenge) & self.randomizer.is_equal(&candidate_randomizer)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use console::{test_crypto_rng, Rng, Uniform};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 100;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            let private_key = snarkvm_console_account::PrivateKey::<<Circuit as Environment>::Network>::new(rng)?;
            let view_key =
                snarkvm_console_account::ViewKey::<<Circuit as Environment>::Network>::try_from(&private_key)?;
            let address = snarkvm_console_account::Address::<<Circuit as Environment>::Network>::try_from(&view_key)?;

            // Compute the native randomizer.
            let serial_numbers = (0..rng.gen_range(0..255i32)).map(|_| Uniform::rand(rng)).collect::<Vec<_>>();
            let output_index = Uniform::rand(rng);
            let randomizer = console::Randomizer::<<Circuit as Environment>::Network>::prove(
                &view_key,
                &serial_numbers,
                output_index,
                rng,
            )?;
            let serial_numbers_digest =
                <<Circuit as Environment>::Network as snarkvm_console_network::Network>::hash_bhp1024(
                    &serial_numbers.to_bits_le(),
                )?;
            assert!(randomizer.verify(&address, serial_numbers_digest, output_index));

            // Inject the randomizer and its arguments into circuits.
            let address = Address::<Circuit>::new(mode, address);
            let serial_numbers_digest = Field::new(mode, serial_numbers_digest);
            let output_index = U16::new(mode, output_index);
            let randomizer = Randomizer::new(mode, randomizer);

            Circuit::scope(format!("Randomizer {i}"), || {
                let candidate = randomizer.verify(&address, &serial_numbers_digest, &output_index);
                assert!(candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_prove_and_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 9669, 0, 0, 0)
    }

    #[test]
    fn test_prove_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 5148, 0, 13744, 13768)
    }

    #[test]
    fn test_prove_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 5148, 0, 13744, 13768)
    }
}
