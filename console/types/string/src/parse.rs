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

        // After this function, we generate a random string and we parse it,
        // testing that we get back the original string.
        // Since our string parser rejects certain characters in strings
        // (see Sanitizer::parse_safe_char),
        // we must avoid generating those characters in the first place.
        // This function, which is called on every randomly generated character,
        // leaves allowed characters unchanged,
        // but adjusts disallowed ones to something allowed (we pick '0').
        // Note that the randomness of the characters is just for testing purposes
        // (there is no cryptographic requirement on this randomness),
        // so the slight bias towards the character '0' does not matter.
        // We could modify this function to adjust disallowed characters differently.
        // But note that the disallowed characters are very few, among all possible characters;
        // so it does not matter too much.
        fn adjust_forbidden_char(ch: char) -> char {
            let code = ch as u32;
            if code < 9
                || code == 11
                || code == 12
                || (14..=31).contains(&code)
                || code == 127
                || (0x202a..=0x202e).contains(&code)
                || (0x2066..=0x2069).contains(&code)
            {
                '0'
            } else {
                ch
            }
        }

        // Aside from the characters rejected through the function adjust_forbidden_char above,
        // the syntax of strings allows backslash and double quotes only in certain circumstances:
        // backslash is used to introduce an escape,
        // and there are constraints on what can occur after a backslash;
        // double quotes is only used in escaped form just after a backslash.
        // If we randomly generate characters, we may end up generating
        // backslashes with malformed escape syntax,
        // or double quotes not preceded by backslash.
        // Thus, we also adjust backslashes and double quotes as we randomly generate characters.
        // See the discussion for adjust_forbidden_char regarding randomness and bias.
        // Note that, this way, we do not test the parsing of any escape sequences;
        // to do that, we would need to reify the possible elements of strings,
        // namely characters and escapes,
        // and randomly generate such elements.
        fn adjust_backslash_and_doublequote(ch: char) -> char {
            if ch == '\\' || ch == '\"' { '0' } else { ch }
        }

        let rng = &mut TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random string. Take 1/4th to ensure we fit for all code points.
            let expected: String = (0..(CurrentEnvironment::MAX_STRING_BYTES - i) / 4)
                .map(|_| rng.gen::<char>())
                .map(adjust_forbidden_char)
                .map(adjust_backslash_and_doublequote)
                .collect();
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
