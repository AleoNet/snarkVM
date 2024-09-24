// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment> Parser for StringType<E> {
    /// Parses a string into a string type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the starting and ending quote '"' keyword from the string.
        let (string, value) = string_parser::parse_string(string)?;

        Ok((string, StringType::new(&value)))
    }
}

impl<E: Environment> FromStr for StringType<E> {
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

impl<E: Environment> Debug for StringType<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<E: Environment> Display for StringType<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "\"{}\"", self.string)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u32 = 100;

    #[test]
    fn test_display() -> Result<()> {
        // Ensure type and empty value fails.
        assert!(StringType::<CurrentEnvironment>::parse(StringType::<CurrentEnvironment>::type_name()).is_err());
        assert!(StringType::<CurrentEnvironment>::parse("").is_err());

        // Ensure empty string succeeds.
        assert!(StringType::<CurrentEnvironment>::parse("\"\"").is_ok());

        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let expected = rng.next_string(CurrentEnvironment::MAX_STRING_BYTES / 4, false);
            let expected_num_bytes = expected.len();
            assert!(expected_num_bytes <= CurrentEnvironment::MAX_STRING_BYTES as usize);

            let candidate = StringType::<CurrentEnvironment>::new(&expected);
            assert_eq!(format!("\"{expected}\""), format!("{candidate}"));

            let candidate_recovered = StringType::<CurrentEnvironment>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }
        Ok(())
    }

    #[test]
    fn test_parse_unsupported_code_points() -> Result<()> {
        const UNSUPPORTED_CODE_POINTS: [&str; 9] = [
            "\u{202a}", "\u{202b}", "\u{202c}", "\u{202d}", "\u{202e}", "\u{2066}", "\u{2067}", "\u{2068}", "\u{2069}",
        ];

        // Ensure that the invalid code point is not allowed in the string.
        for unsupported_code_point in UNSUPPORTED_CODE_POINTS {
            assert!(StringType::<CurrentEnvironment>::parse(unsupported_code_point).is_err());
        }

        Ok(())
    }
}
