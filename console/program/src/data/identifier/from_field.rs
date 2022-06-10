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

impl<N: Network> FromField for Identifier<N> {
    type Field = Field<N>;

    /// Initializes a new identifier from a field element.
    fn from_field(field: &Self::Field) -> Result<Self> {
        // Convert the field to a list of little-endian bits.
        Self::from_bits_le(&field.to_bits_le())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::identifier::tests::sample_identifier;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_from_field() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric identifier, that always starts with an alphabetic character.
            let identifier = sample_identifier::<CurrentNetwork>()?;
            assert_eq!(identifier, Identifier::from_field(&identifier.to_field()?)?);
        }
        Ok(())
    }
}
