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

impl<N: Network> Parser for Import<N> {
    /// Parses a string into an import statement of the form `import {name}.{network};`.
    /// If no `network`-level domain is specified, the default network is used.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the import keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the program ID from the string.
        let (string, id) = ProgramID::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon from the string.
        let (string, _) = tag(";")(string)?;
        // Return the import statement.
        Ok((string, Self { program_id: id }))
    }
}

impl<N: Network> FromStr for Import<N> {
    type Err = Error;

    /// Parses a string into an import statement.
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

impl<N: Network> Debug for Import<N> {
    /// Prints the import as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Import<N> {
    /// Prints the import statement as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{type_} {id};", type_ = Self::type_name(), id = self.program_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_import_parse() -> Result<()> {
        let import = Import::<CurrentNetwork>::parse("import bar.aleo;").unwrap().1;
        assert_eq!(import.name(), &Identifier::<CurrentNetwork>::from_str("bar")?);
        assert_eq!(import.network(), &Identifier::<CurrentNetwork>::from_str("aleo")?);

        let import = Import::<CurrentNetwork>::parse("import foo.aleo;").unwrap().1;
        assert_eq!(import.name(), &Identifier::<CurrentNetwork>::from_str("foo")?);
        assert_eq!(import.network(), &Identifier::<CurrentNetwork>::from_str("aleo")?);

        Ok(())
    }

    #[test]
    fn test_import_display() -> Result<()> {
        let import = Import::<CurrentNetwork>::from_str("import bar.aleo;")?;
        assert_eq!("import bar.aleo;", import.to_string());

        let import = Import::<CurrentNetwork>::from_str("import foo.aleo;")?;
        assert_eq!("import foo.aleo;", import.to_string());

        Ok(())
    }
}
