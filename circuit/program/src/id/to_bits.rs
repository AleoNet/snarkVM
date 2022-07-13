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

impl<A: Aleo> ToBits for ProgramID<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the program ID.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_le()
    }

    /// Returns the big-endian bits of the program ID.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<A: Aleo> ToBits for &ProgramID<A> {
    type Boolean = Boolean<A>;

    /// Returns the little-endian bits of the program ID.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let mut bits = self.name().to_bits_le();
        bits.extend(self.network().to_bits_le());
        bits
    }

    /// Returns the big-endian bits of the program ID.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let mut bits = self.name().to_bits_be();
        bits.extend(self.network().to_bits_be());
        bits
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{data::identifier::tests::sample_console_identifier_as_string, Circuit};

    use anyhow::Result;

    const ITERATIONS: usize = 100;

    fn check_to_bits_le(mode: Mode) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_name_string = sample_console_identifier_as_string::<Circuit>()?;
            let expected = console::ProgramID::<<Circuit as Environment>::Network>::from_str(&format!(
                "{expected_name_string}.aleo"
            ))?;

            let candidate = ProgramID::<Circuit>::new(mode, expected);
            assert_eq!(expected.to_bits_le(), candidate.to_bits_le().eject_value());
        }
        Ok(())
    }

    fn check_to_bits_be(mode: Mode) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_name_string = sample_console_identifier_as_string::<Circuit>()?;
            let expected = console::ProgramID::<<Circuit as Environment>::Network>::from_str(&format!(
                "{expected_name_string}.aleo"
            ))?;

            let candidate = ProgramID::<Circuit>::new(mode, expected);
            assert_eq!(expected.to_bits_be(), candidate.to_bits_be().eject_value());
        }
        Ok(())
    }

    #[test]
    fn test_to_bits_le() -> Result<()> {
        check_to_bits_le(Mode::Constant)?;
        check_to_bits_le(Mode::Public)?;
        check_to_bits_le(Mode::Private)?;
        Ok(())
    }

    #[test]
    fn test_to_bits_be() -> Result<()> {
        check_to_bits_be(Mode::Constant)?;
        check_to_bits_be(Mode::Public)?;
        check_to_bits_be(Mode::Private)?;
        Ok(())
    }
}
