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
    /// Returns `true` if the proof is valid, and `false` otherwise.
    pub fn verify(&self, pk_vrf: &Group<A>, state: &State<A>) -> Boolean<A> {
        // Retrieve the proof components.
        let (gamma, challenge, response) = &self.proof;

        // Compute the state digest.
        let state_digest = state.to_digest();

        // Compute the generator `H` as `HashToGroup(state_digest)`.
        let generator_h = A::hash_to_group_psd4(&[A::serial_number_domain(), state_digest.clone()]);

        // Compute `u` as `(challenge * address) + (response * G)`, equivalent to `nonce * G`.
        let u = (pk_vrf * challenge) + A::g_scalar_multiply(response);

        // Compute `v` as `(challenge * gamma) + (response * H)`, equivalent to `nonce * H`.
        let v = (gamma * challenge) + (generator_h * response);

        // Compute `candidate_challenge` as `HashToScalar(address, gamma, nonce * G, nonce * H)`.
        let candidate_challenge = A::hash_to_scalar_psd4(&[pk_vrf, gamma, &u, &v].map(|c| c.to_x_coordinate()));

        // Compute `candidate_serial_number_nonce` as `HashToScalar(COFACTOR * gamma)`.
        let candidate_serial_number_nonce =
            A::hash_to_scalar_psd2(&[A::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);

        // Compute `candidate_serial_number` as `Commit( (state_digest), serial_number_nonce )`.
        let candidate_serial_number =
            A::commit_bhp512(&(&A::serial_number_domain(), &state_digest).to_bits_le(), &candidate_serial_number_nonce);

        // Return `true` the challenge and serial number is valid.
        challenge.is_equal(&candidate_challenge) & self.serial_number.is_equal(&candidate_serial_number)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_network::AleoV0;
    use snarkvm_utilities::{test_crypto_rng, Rng, ToBits as T, UniformRand};

    use anyhow::Result;

    type Circuit = AleoV0;

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
            // Compute the native serial number.
            let sk_vrf = UniformRand::rand(rng);
            let state = console::State::from(
                UniformRand::rand(rng),
                UniformRand::rand(rng),
                snarkvm_console_account::Address::from_group(UniformRand::rand(rng)),
                UniformRand::rand(rng),
                UniformRand::rand(rng),
                UniformRand::rand(rng),
            );

            let pk_vrf =
                <<Circuit as Environment>::Network as snarkvm_console_network::Network>::g_scalar_multiply(&sk_vrf)
                    .into();

            let serial_number =
                console::SerialNumber::<<Circuit as Environment>::Network>::prove(&sk_vrf, &state, rng)?;
            assert!(serial_number.verify(&pk_vrf, &state));

            // Inject the serial number and its arguments into circuits.
            let pk_vrf = Group::<Circuit>::new(mode, pk_vrf);
            let state = State::new(mode, state);
            let serial_number = SerialNumber::new(mode, serial_number);

            Circuit::scope(format!("SerialNumber {i}"), || {
                let candidate = serial_number.verify(&pk_vrf, &state);
                assert!(candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_prove_and_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 37325, 0, 0, 0)
    }

    #[test]
    fn test_prove_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 29002, 0, 19689, 19718)
    }

    #[test]
    fn test_prove_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 29002, 0, 19689, 19718)
    }
}
