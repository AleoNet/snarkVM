// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> Parser for Finalize<N> {
    /// Parses a string into finalize.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'finalize' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the associated function name from the string.
        let (string, name) = Identifier::<N>::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the colon ':' keyword from the string.
        let (string, _) = tag(":")(string)?;

        // Parse the inputs from the string.
        let (string, inputs) = many0(Input::parse)(string)?;
        // Parse the commands from the string.
        let (string, commands) = many1(Command::parse)(string)?;

        map_res(take(0usize), move |_| {
            // Initialize a new finalize.
            let mut finalize = Self::new(name);
            if let Err(error) = inputs.iter().cloned().try_for_each(|input| finalize.add_input(input)) {
                eprintln!("{error}");
                return Err(error);
            }
            if let Err(error) = commands.iter().cloned().try_for_each(|command| finalize.add_command(command)) {
                eprintln!("{error}");
                return Err(error);
            }
            Ok::<_, Error>(finalize)
        })(string)
    }
}

impl<N: Network> FromStr for Finalize<N> {
    type Err = Error;

    /// Returns a finalize from a string literal.
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

impl<N: Network> Debug for Finalize<N> {
    /// Prints the finalize as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Finalize<N> {
    /// Prints the finalize as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Write the finalize to a string.
        write!(f, "{} {}:", Self::type_name(), self.name)?;
        self.inputs.iter().try_for_each(|input| write!(f, "\n    {input}"))?;
        self.commands.iter().try_for_each(|command| write!(f, "\n    {command}"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_finalize_parse() {
        let finalize = Finalize::<CurrentNetwork>::parse(
            r"
finalize foo:
    input r0 as field.public;
    input r1 as field.public;
    add r0 r1 into r2;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", finalize.name().to_string());
        assert_eq!(2, finalize.inputs.len());
        assert_eq!(1, finalize.commands.len());

        // Finalize with 0 inputs.
        let finalize = Finalize::<CurrentNetwork>::parse(
            r"
finalize foo:
    add 1u32 2u32 into r0;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", finalize.name().to_string());
        assert_eq!(0, finalize.inputs.len());
        assert_eq!(1, finalize.commands.len());
    }

    #[test]
    fn test_finalize_parse_cast() {
        let finalize = Finalize::<CurrentNetwork>::parse(
            r"
finalize foo:
    input r0 as token.public;
    cast r0.owner r0.token_amount into r1 as token;",
        )
        .unwrap()
        .1;
        assert_eq!("foo", finalize.name().to_string());
        assert_eq!(1, finalize.inputs.len());
        assert_eq!(1, finalize.commands.len());
    }

    #[test]
    fn test_finalize_display() {
        let expected = r"finalize foo:
    input r0 as field.public;
    input r1 as field.public;
    add r0 r1 into r2;";
        let finalize = Finalize::<CurrentNetwork>::parse(expected).unwrap().1;
        assert_eq!(expected, format!("{finalize}"),);
    }
}
