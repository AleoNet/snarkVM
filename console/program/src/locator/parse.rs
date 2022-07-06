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
        // Parse the optional "/" and resource from the string.
        let (string, resource) = opt(pair(tag("/"), Identifier::parse))(string)?;
        // Return the locator.
        match resource {
            Some((_, resource)) => Ok((string, Self { id, resource: Some(resource) })),
            None => Ok((string, Self { id, resource: None })),
        }
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
        match self.resource {
            Some(resource) => write!(f, "{id}/{resource}", id = self.id),
            None => write!(f, "{id}", id = self.id),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_import_parse() -> Result<()> {
        let locator = Locator::<CurrentNetwork>::parse("foo.aleo").unwrap().1;
        assert_eq!(locator.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(locator.network(), Identifier::<CurrentNetwork>::from_str("aleo")?);
        assert_eq!(locator.resource(), &None);

        let locator = Locator::<CurrentNetwork>::parse("foo.aleo/compute").unwrap().1;
        assert_eq!(locator.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(locator.network(), Identifier::<CurrentNetwork>::from_str("aleo")?);
        assert_eq!(locator.resource(), &Some(Identifier::<CurrentNetwork>::from_str("compute")?));

        let locator = Locator::<CurrentNetwork>::parse("foo/compute").unwrap().1;
        assert_eq!(locator.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(locator.network(), Identifier::<CurrentNetwork>::from_str("aleo")?);
        assert_eq!(locator.resource(), &Some(Identifier::<CurrentNetwork>::from_str("compute")?));

        Ok(())
    }

    #[test]
    fn test_import_display() -> Result<()> {
        let id = Locator::<CurrentNetwork>::from_str("foo.aleo")?;
        assert_eq!("foo.aleo", id.to_string());

        let id = Locator::<CurrentNetwork>::from_str("foo.aleo/compute")?;
        assert_eq!("foo.aleo/compute", id.to_string());

        let id = Locator::<CurrentNetwork>::from_str("foo/compute")?;
        assert_eq!("foo.aleo/compute", id.to_string());

        Ok(())
    }
}
