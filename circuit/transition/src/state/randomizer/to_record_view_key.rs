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
    /// Returns the record view key given the account address.
    pub fn to_record_view_key(&self, address: &Address<A>) -> Field<A> {
        // Compute the record view key as `randomizer * address`.
        (address.to_group() * &self.randomizer).to_x_coordinate()
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_crypto_rng, Rng, UniformRand};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 100;

    fn check_to_nonce(
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
            let serial_numbers = (0..rng.gen_range(0..255)).map(|_| UniformRand::rand(rng)).collect::<Vec<_>>();
            let output_index = UniformRand::rand(rng);
            let randomizer = console::Randomizer::<<Circuit as Environment>::Network>::prove(
                &view_key,
                &serial_numbers,
                output_index,
                rng,
            )?;
            let expected = randomizer.to_record_view_key(&address);

            // Inject the address and randomizer.
            let address = Address::<Circuit>::new(mode, address);
            let randomizer = Randomizer::<Circuit>::new(mode, randomizer);

            Circuit::scope(format!("Randomizer {i}"), || {
                let candidate = randomizer.to_record_view_key(&address);
                assert_eq!(expected, candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_to_nonce_constant() -> Result<()> {
        check_to_nonce(Mode::Constant, 1743, 0, 0, 0)
    }

    #[test]
    fn test_to_nonce_public() -> Result<()> {
        check_to_nonce(Mode::Public, 750, 0, 3252, 3252)
    }

    #[test]
    fn test_to_nonce_private() -> Result<()> {
        check_to_nonce(Mode::Private, 750, 0, 3252, 3252)
    }
}
