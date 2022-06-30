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

impl<E: Environment> Parser for Scalar<E> {
    /// Parses a string into a scalar circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value): (&str, E::Scalar) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Negate the value if the negative sign was present.
        let value = match negation {
            true => -value,
            false => value,
        };

        Ok((string, Scalar::new(value)))
    }
}

impl<E: Environment> FromStr for Scalar<E> {
    type Err = Error;

    /// Parses a string into a scalar.
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

impl<E: Environment> Debug for Scalar<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<E: Environment> Display for Scalar<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.scalar, Self::type_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_parse() -> Result<()> {
        let rng = &mut test_rng();

        // Ensure empty value fails.
        assert!(Scalar::<CurrentEnvironment>::parse(Scalar::<CurrentEnvironment>::type_name()).is_err());
        assert!(Scalar::<CurrentEnvironment>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let scalar: <CurrentEnvironment as Environment>::Scalar = Uniform::rand(rng);

            let expected = format!("{}{}", scalar, Scalar::<CurrentEnvironment>::type_name());
            let (remainder, candidate) = Scalar::<CurrentEnvironment>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a scalar from the given element,
        /// format it in display mode, and recover a scalar from it.
        fn check_display<E: Environment>(element: E::Scalar) {
            let candidate = Scalar::<E>::new(element);
            assert_eq!(format!("{element}{}", Scalar::<E>::type_name()), format!("{candidate}"));

            let candidate_recovered = Scalar::<E>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        for _ in 0..ITERATIONS {
            let element = Uniform::rand(&mut test_rng());

            check_display::<CurrentEnvironment>(element);
        }
    }

    #[test]
    fn test_display_zero() {
        let zero = <CurrentEnvironment as Environment>::Scalar::zero();

        let candidate = Scalar::<CurrentEnvironment>::new(zero);
        assert_eq!("0scalar", &format!("{}", candidate));
    }

    #[test]
    fn test_display_one() {
        let one = <CurrentEnvironment as Environment>::Scalar::one();

        let candidate = Scalar::<CurrentEnvironment>::new(one);
        assert_eq!("1scalar", &format!("{}", candidate));
    }

    #[test]
    fn test_display_two() {
        let one = <CurrentEnvironment as Environment>::Scalar::one();
        let two = one + one;

        let candidate = Scalar::<CurrentEnvironment>::new(two);
        assert_eq!("2scalar", &format!("{}", candidate));
    }
}
