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
        let (string, network) = opt(pair(tag("."), Identifier::parse))(string)?;
        // Return the program ID.
        match network {
            Some((_, network)) => Ok((string, Self { name, network: Some(network) })),
            None => Ok((string, Self { name, network: None })),
        }
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
        match self.network {
            Some(network) => write!(f, "{name}.{network}", name = self.name, network = network),
            None => write!(f, "{name}.aleo", name = self.name),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_import_parse() -> Result<()> {
        let import = ProgramID::<CurrentNetwork>::parse("bar.aleo").unwrap().1;
        assert_eq!(import.name(), &Identifier::<CurrentNetwork>::from_str("bar")?);
        assert_eq!(import.network()?, Identifier::<CurrentNetwork>::from_str("aleo")?);

        let import = ProgramID::<CurrentNetwork>::parse("foo").unwrap().1;
        assert_eq!(import.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(import.network()?, Identifier::<CurrentNetwork>::from_str("aleo")?);

        Ok(())
    }

    #[test]
    fn test_import_display() -> Result<()> {
        let import = ProgramID::<CurrentNetwork>::from_str("bar.aleo")?;
        assert_eq!("bar.aleo", import.to_string());

        let import = ProgramID::<CurrentNetwork>::from_str("foo")?;
        assert_eq!("foo.aleo", import.to_string());

        Ok(())
    }
}
