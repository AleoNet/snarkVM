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

impl<N: Network> Parser for Field<N> {
    /// Parses a string into a field circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value): (&str, N::Field) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Negate the value if the negative sign was present.
        let value = match negation {
            true => -value,
            false => value,
        };

        Ok((string, Field::new(value)))
    }
}

impl<N: Network> FromStr for Field<N> {
    type Err = Error;

    /// Parses a string into a field.
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

impl<N: Network> Debug for Field<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Field<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.field, Self::type_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_parse() -> Result<()> {
        let rng = &mut test_rng();

        // Ensure empty value fails.
        assert!(Field::<CurrentNetwork>::parse(&Field::<CurrentNetwork>::type_name()).is_err());
        assert!(Field::<CurrentNetwork>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let field: <CurrentNetwork as Network>::Field = Uniform::rand(rng);

            let expected = format!("{}{}", field, Field::<CurrentNetwork>::type_name());
            let (remainder, candidate) = Field::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a field from the given element,
        /// format it in display mode, and recover a field from it.
        fn check_display<N: Network>(element: N::Field) {
            let candidate = Field::<N>::new(element);
            assert_eq!(format!("{element}{}", Field::<N>::type_name()), format!("{candidate}"));

            let candidate_recovered = Field::<N>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        for _ in 0..ITERATIONS {
            let element = Uniform::rand(&mut test_rng());

            check_display::<CurrentNetwork>(element);
        }
    }

    #[test]
    fn test_display_zero() {
        let zero = <CurrentNetwork as Network>::Field::zero();

        let candidate = Field::<CurrentNetwork>::new(zero);
        assert_eq!("0field", &format!("{}", candidate));
    }

    #[test]
    fn test_display_one() {
        let one = <CurrentNetwork as Network>::Field::one();

        let candidate = Field::<CurrentNetwork>::new(one);
        assert_eq!("1field", &format!("{}", candidate));
    }

    #[test]
    fn test_display_two() {
        let one = <CurrentNetwork as Network>::Field::one();
        let two = one + one;

        let candidate = Field::<CurrentNetwork>::new(two);
        assert_eq!("2field", &format!("{}", candidate));
    }
}
