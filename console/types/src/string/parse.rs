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

impl<N: Network> Parser for StringType<N> {
    /// Parses a string into a string type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the starting and ending quote '"' keyword from the string.
        let (string, value) = string_parser::parse_string(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, StringType::new(mode, &value))),
            None => Ok((string, StringType::new(Mode::Constant, &value))),
        }
    }
}

impl<N: Network> FromStr for StringType<N> {
    type Err = Error;

    /// Parses a string into a string type.
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

impl<N: Network> Debug for StringType<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for StringType<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "\"{}\".{}", self.string, self.mode)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 100;

    #[test]
    fn test_display() -> Result<()> {
        /// Attempts to construct an string from the given native string and mode,
        /// format it in display mode, and recover an string from it.
        fn check_display<N: Network>(mode: Mode, string: &str) {
            let candidate = StringType::<N>::new(mode, string);
            assert_eq!(format!("\"{string}\".{mode}"), format!("{candidate}"));

            let candidate_recovered = StringType::<N>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        // Ensure type and empty value fails.
        assert!(StringType::<CurrentNetwork>::parse(&StringType::<CurrentNetwork>::type_name()).is_err());
        assert!(StringType::<CurrentNetwork>::parse("").is_err());

        // Ensure empty string succeeds.
        assert!(StringType::<CurrentNetwork>::parse("\"\"").is_ok());

        let rng = &mut test_rng();

        for i in 0..ITERATIONS {
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let expected: String = (0..(CurrentNetwork::MAX_STRING_BYTES - i) / 4).map(|_| rng.gen::<char>()).collect();
            let expected_num_bytes = expected.len();
            assert!(expected_num_bytes <= CurrentNetwork::MAX_STRING_BYTES as usize);

            // Constant
            check_display::<CurrentNetwork>(Mode::Constant, &expected);
            // Public
            check_display::<CurrentNetwork>(Mode::Public, &expected);
            // Private
            check_display::<CurrentNetwork>(Mode::Private, &expected);
        }
        Ok(())
    }
}
