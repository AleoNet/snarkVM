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

impl<N: Network> Parser for Boolean<N> {
    /// Parses a string into a boolean circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the boolean from the string.
        let (string, value) = alt((map(tag("true"), |_| true), map(tag("false"), |_| false)))(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Boolean::new(mode, value))),
            None => Ok((string, Boolean::new(Mode::Constant, value))),
        }
    }
}

impl<N: Network> FromStr for Boolean<N> {
    type Err = Error;

    /// Parses a string into a mode.
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

impl<N: Network> Debug for Boolean<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Boolean<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.boolean, self.mode)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_parse() -> Result<()> {
        for boolean in &[true, false] {
            // Constant mode - A.
            let expected = format!("{}", boolean);
            let (remainder, candidate) = Boolean::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}.constant"), candidate.to_string());
            assert_eq!("", remainder);

            // Constant mode - B.
            let expected = format!("{}.constant", boolean);
            let (remainder, candidate) = Boolean::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);

            // Public mode.
            let expected = format!("{}.public", boolean);
            let (remainder, candidate) = Boolean::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);

            // Private mode.
            let expected = format!("{}.private", boolean);
            let (remainder, candidate) = Boolean::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a boolean from the given element and mode,
        /// format it in display mode, and recover a boolean from it.
        fn check_display<N: Network>(mode: Mode, element: bool) {
            let candidate = Boolean::<N>::new(mode, element);
            assert_eq!(format!("{element}.{mode}"), format!("{candidate}"));

            let candidate_recovered = Boolean::<N>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        // Constant
        check_display::<CurrentNetwork>(Mode::Constant, false);
        check_display::<CurrentNetwork>(Mode::Constant, true);
        // Public
        check_display::<CurrentNetwork>(Mode::Public, false);
        check_display::<CurrentNetwork>(Mode::Public, true);
        // Private
        check_display::<CurrentNetwork>(Mode::Private, false);
        check_display::<CurrentNetwork>(Mode::Private, true);
    }

    #[test]
    fn test_display_false() {
        // Constant
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Constant, false);
        assert_eq!("false.constant", &format!("{}", candidate));

        // Public
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Public, false);
        assert_eq!("false.public", &format!("{}", candidate));

        // Private
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Private, false);
        assert_eq!("false.private", &format!("{}", candidate));
    }

    #[test]
    fn test_display_true() {
        // Constant
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Constant, true);
        assert_eq!("true.constant", &format!("{}", candidate));

        // Public
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Public, true);
        assert_eq!("true.public", &format!("{}", candidate));

        // Private
        let candidate = Boolean::<CurrentNetwork>::new(Mode::Private, true);
        assert_eq!("true.private", &format!("{}", candidate));
    }
}
