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

impl<A: Aleo> ToBits for Identifier<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the identifier.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.0.to_bits_le()[..8 * self.1 as usize].to_vec()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits = self.to_bits_le();
        bits.reverse();
        bits
    }
}

impl<A: Aleo> ToBits for &Identifier<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the identifier.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        self.0.to_bits_le()[..8 * self.1 as usize].to_vec()
    }

    /// Returns the big-endian bits of the identifier.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits = self.to_bits_le();
        bits.reverse();
        bits
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{data::identifier::tests::sample_console_identifier, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_to_bits_le(num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Initialize the console identifier.
            let console_identifier = sample_console_identifier::<Circuit>()?;
            // Initialize the circuit identifier.
            let circuit_identifier = Identifier::<Circuit>::new(Mode::Constant, console_identifier);

            Circuit::scope("Identifier ToBits", || {
                let candidate = circuit_identifier.to_bits_le();
                assert_eq!(Mode::Constant, candidate.eject_mode());
                assert_eq!(console_identifier.to_bits_le(), candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    fn check_to_bits_be(num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Initialize the console identifier.
            let console_identifier = sample_console_identifier::<Circuit>()?;
            // Initialize the circuit identifier.
            let circuit_identifier = Identifier::<Circuit>::new(Mode::Constant, console_identifier);

            Circuit::scope("Identifier ToBits", || {
                let candidate = circuit_identifier.to_bits_be();
                assert_eq!(Mode::Constant, candidate.eject_mode());
                assert_eq!(console_identifier.to_bits_be(), candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_to_bits_le() -> Result<()> {
        check_to_bits_le(0, 0, 0, 0)
    }

    #[test]
    fn test_to_bits_be() -> Result<()> {
        check_to_bits_be(0, 0, 0, 0)
    }
}
