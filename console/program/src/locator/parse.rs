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

impl<N: Network> Parser for Locator<N> {
    /// Parses a string into a locator of the form `{program_id}/{resource}`.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the program ID from the string.
        let (string, id) = ProgramID::parse(string)?;
        // Parse the "/" and resource from the string.
        let (string, (_, resource)) = pair(tag("/"), Identifier::parse)(string)?;
        // Return the locator.
        Ok((string, Self { id, resource }))
    }
}

impl<N: Network> FromStr for Locator<N> {
    type Err = Error;

    /// Parses a string into a locator.
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

impl<N: Network> Debug for Locator<N> {
    /// Prints the locator as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Locator<N> {
    /// Prints the locator as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{id}/{resource}", id = self.id, resource = self.resource)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_import_parse() -> Result<()> {
        let locator = Locator::<CurrentNetwork>::parse("foo.aleo/compute").unwrap().1;
        assert_eq!(locator.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(locator.network(), &Identifier::<CurrentNetwork>::from_str("aleo")?);
        assert_eq!(locator.resource(), &Identifier::<CurrentNetwork>::from_str("compute")?);

        assert!(Locator::<CurrentNetwork>::parse("foo.aleo").is_err());
        assert!(Locator::<CurrentNetwork>::parse("foo/compute").is_err());

        Ok(())
    }

    #[test]
    fn test_import_display() -> Result<()> {
        let id = Locator::<CurrentNetwork>::from_str("foo.aleo/compute")?;
        assert_eq!("foo.aleo/compute", id.to_string());

        assert!(Locator::<CurrentNetwork>::parse("foo.aleo").is_err());
        assert!(Locator::<CurrentNetwork>::parse("foo/compute").is_err());

        Ok(())
    }
}
