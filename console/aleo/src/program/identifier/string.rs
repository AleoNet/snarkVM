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

impl<N: Network> FromStr for Identifier<N> {
    type Err = Error;

    /// Reads in an identifier from a string.
    fn from_str(identifier: &str) -> Result<Self, Self::Err> {
        // Ensure the identifier is not an empty string, and does not start with a number.
        match identifier.chars().next() {
            Some(character) => {
                if character.is_numeric() {
                    bail!("Identifier cannot start with a number")
                }
            }
            None => bail!("Identifier cannot be an empty string"),
        }

        // Ensure the identifier is alphanumeric and underscores.
        if !identifier.chars().all(|character| character.is_alphanumeric() || character == '_') {
            bail!("Identifier must be alphanumeric and underscores")
        }

        // Ensure the identifier is not solely underscores.
        if identifier.chars().all(|character| character == '_') {
            bail!("Identifier cannot consist solely of underscores")
        }

        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = N::Field::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        if identifier.len() > max_bytes {
            bail!("Identifier is too large. Identifiers must be <= {max_bytes} bytes long")
        }

        // Return the identifier.
        Ok(Self(identifier.to_string(), PhantomData))
    }
}

impl<N: Network> fmt::Display for Identifier<N> {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Testnet3;
    use snarkvm_utilities::{test_rng, Rng};

    use rand::distributions::Alphanumeric;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: usize = 100;

    #[test]
    fn test_identifier_from_str() -> Result<()> {
        let candidate = Identifier::<CurrentNetwork>::from_str("foo_bar").unwrap();
        assert_eq!("foo_bar", candidate.0);

        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let string = "a".to_string()
                + &rng
                    .sample_iter(&Alphanumeric)
                    .take(<CurrentNetwork as Network>::Field::size_in_data_bits() / (8 * 2))
                    .map(char::from)
                    .collect::<String>();
            let expected = Identifier::<CurrentNetwork>::from_str(&string)?;

            let candidate = Identifier::<CurrentNetwork>::from_str(&string)?;
            assert_eq!(expected, candidate);
            assert_eq!(string, candidate.to_string());
        }
        Ok(())
    }

    #[test]
    fn test_identifier_from_str_fails() {
        // Must be alphanumeric or underscore.
        assert!(Identifier::<CurrentNetwork>::from_str("foo_bar~baz").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("foo_bar-baz").is_err());

        // Must not be solely underscores.
        assert!(Identifier::<CurrentNetwork>::from_str("_").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("__").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("___").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("____").is_err());

        // Must not start with a number.
        assert!(Identifier::<CurrentNetwork>::from_str("1").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("2").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("3").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("1foo").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("12").is_err());
        assert!(Identifier::<CurrentNetwork>::from_str("111").is_err());

        // Must fit within the data capacity of a base field element.
        let identifier = Identifier::<CurrentNetwork>::from_str(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy",
        );
        assert!(identifier.is_err());
    }

    #[test]
    fn test_identifier_display() -> Result<()> {
        let identifier = Identifier::<CurrentNetwork>::from_str("foo_bar")?;
        assert_eq!("foo_bar", format!("{identifier}"));
        Ok(())
    }
}
