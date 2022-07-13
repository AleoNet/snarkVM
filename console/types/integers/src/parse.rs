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

impl<E: Environment, I: IntegerType> Parser for Integer<E, I> {
    /// Parses a string into a integer circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.unwrap_or_default().to_string())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Combine the sign and primitive.
        let primitive = negation + primitive;
        // Parse the value from the string.
        let (string, value) = map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;

        Ok((string, Integer::new(value)))
    }
}

impl<E: Environment, I: IntegerType> FromStr for Integer<E, I> {
    type Err = Error;

    /// Parses a string into an integer.
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

impl<E: Environment, I: IntegerType> Debug for Integer<E, I> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<E: Environment, I: IntegerType> Display for Integer<E, I> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.integer, Self::type_name())
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
        assert!(Integer::<CurrentEnvironment, i8>::parse(Integer::<CurrentEnvironment, i8>::type_name()).is_err());
        assert!(Integer::<CurrentEnvironment, i8>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let integer: i8 = Uniform::rand(rng);

            let expected = format!("{}{}", integer, Integer::<CurrentEnvironment, i8>::type_name());
            let (remainder, candidate) = Integer::<CurrentEnvironment, i8>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a integer from the given element,
        /// format it in display mode, and recover a integer from it.
        fn check_display<E: Environment, I: IntegerType>() {
            for _ in 0..ITERATIONS {
                let element = Uniform::rand(&mut test_rng());

                let candidate = Integer::<E, I>::new(element);
                assert_eq!(format!("{element}{}", Integer::<E, I>::type_name()), format!("{candidate}"));

                let candidate_recovered = Integer::<E, I>::from_str(&format!("{candidate}")).unwrap();
                assert_eq!(candidate, candidate_recovered);
            }
        }

        check_display::<CurrentEnvironment, u8>();
        check_display::<CurrentEnvironment, u16>();
        check_display::<CurrentEnvironment, u32>();
        check_display::<CurrentEnvironment, u64>();
        check_display::<CurrentEnvironment, u128>();

        check_display::<CurrentEnvironment, i8>();
        check_display::<CurrentEnvironment, i16>();
        check_display::<CurrentEnvironment, i32>();
        check_display::<CurrentEnvironment, i64>();
        check_display::<CurrentEnvironment, i128>();
    }

    #[test]
    fn test_display_zero() {
        let zero = i8::zero();

        let candidate = Integer::<CurrentEnvironment, i8>::new(zero);
        assert_eq!("0i8", &format!("{}", candidate));
    }

    #[test]
    fn test_display_one() {
        let one = i8::one();

        let candidate = Integer::<CurrentEnvironment, i8>::new(one);
        assert_eq!("1i8", &format!("{}", candidate));
    }

    #[test]
    fn test_display_two() {
        let one = i8::one();
        let two = one + one;

        let candidate = Integer::<CurrentEnvironment, i8>::new(two);
        assert_eq!("2i8", &format!("{}", candidate));
    }
}
