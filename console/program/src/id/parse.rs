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

impl<N: Network> Parser for ProgramID<N> {
    /// Parses a string into a program ID of the form `{name}.{network}`.
    /// If no `network`-level domain is specified, the default network is used.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the name from the string.
        let (string, name) = Identifier::parse(string)?;
        // Parse the optional "." and network-level domain (NLD) from the string.
        let (string, (_, network)) = pair(tag("."), Identifier::parse)(string)?;
        // Return the program ID.
        Ok((string, Self { name, network }))
    }
}

impl<N: Network> FromStr for ProgramID<N> {
    type Err = Error;

    /// Parses a string into a program ID.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for ProgramID<N> {
    /// Prints the program ID as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for ProgramID<N> {
    /// Prints the program ID as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{name}.{network}", name = self.name, network = self.network)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() -> Result<()> {
        let id = ProgramID::<CurrentNetwork>::parse("bar.aleo").unwrap().1;
        assert_eq!(id.name(), &Identifier::<CurrentNetwork>::from_str("bar")?);
        assert_eq!(id.network(), &Identifier::<CurrentNetwork>::from_str("aleo")?);

        assert!(ProgramID::<CurrentNetwork>::parse("foo").is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        let id = ProgramID::<CurrentNetwork>::from_str("bar.aleo")?;
        assert_eq!("bar.aleo", id.to_string());

        assert!(ProgramID::<CurrentNetwork>::from_str("foo").is_err());

        Ok(())
    }
}
