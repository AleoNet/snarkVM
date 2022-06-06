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

impl<N: Network, I: IntegerType> Parser for Integer<N, I> {
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
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Integer::new(mode, value))),
            None => Ok((string, Integer::new(Mode::Constant, value))),
        }
    }
}

impl<N: Network, I: IntegerType> FromStr for Integer<N, I> {
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

impl<N: Network, I: IntegerType> Debug for Integer<N, I> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network, I: IntegerType> Display for Integer<N, I> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}.{}", self.integer, Self::type_name(), self.mode)
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
        assert!(Integer::<CurrentNetwork, i8>::parse(&Integer::<CurrentNetwork, i8>::type_name()).is_err());
        assert!(Integer::<CurrentNetwork, i8>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let integer: i8 = Uniform::rand(rng);

            // Constant mode - A.
            let expected = format!("{}{}", integer, Integer::<CurrentNetwork, i8>::type_name());
            let (remainder, candidate) = Integer::<CurrentNetwork, i8>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}.constant"), candidate.to_string());
            assert_eq!("", remainder);

            // Constant mode - B.
            let expected = format!("{}{}.constant", integer, Integer::<CurrentNetwork, i8>::type_name());
            let (remainder, candidate) = Integer::<CurrentNetwork, i8>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);

            // Public mode.
            let expected = format!("{}{}.public", integer, Integer::<CurrentNetwork, i8>::type_name());
            let (remainder, candidate) = Integer::<CurrentNetwork, i8>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);

            // Private mode.
            let expected = format!("{}{}.private", integer, Integer::<CurrentNetwork, i8>::type_name());
            let (remainder, candidate) = Integer::<CurrentNetwork, i8>::parse(&expected).unwrap();
            assert_eq!(expected, candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a integer from the given element and mode,
        /// format it in display mode, and recover a integer from it.
        fn check_display<N: Network, I: IntegerType>() {
            for _ in 0..ITERATIONS {
                let element = Uniform::rand(&mut test_rng());

                let check_display = |(mode, element)| {
                    let candidate = Integer::<N, I>::new(mode, element);
                    assert_eq!(format!("{element}{}.{mode}", Integer::<N, I>::type_name()), format!("{candidate}"));

                    let candidate_recovered = Integer::<N, I>::from_str(&format!("{candidate}")).unwrap();
                    assert_eq!(candidate, candidate_recovered);
                };

                check_display((Mode::Constant, element));
                check_display((Mode::Public, element));
                check_display((Mode::Private, element));
            }
        }

        check_display::<CurrentNetwork, u8>();
        check_display::<CurrentNetwork, u16>();
        check_display::<CurrentNetwork, u32>();
        check_display::<CurrentNetwork, u64>();
        check_display::<CurrentNetwork, u128>();

        check_display::<CurrentNetwork, i8>();
        check_display::<CurrentNetwork, i16>();
        check_display::<CurrentNetwork, i32>();
        check_display::<CurrentNetwork, i64>();
        check_display::<CurrentNetwork, i128>();
    }

    #[test]
    fn test_display_zero() {
        let zero = i8::zero();

        // Constant
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Constant, zero);
        assert_eq!("0i8.constant", &format!("{}", candidate));

        // Public
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Public, zero);
        assert_eq!("0i8.public", &format!("{}", candidate));

        // Private
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Private, zero);
        assert_eq!("0i8.private", &format!("{}", candidate));
    }

    #[test]
    fn test_display_one() {
        let one = i8::one();

        // Constant
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Constant, one);
        assert_eq!("1i8.constant", &format!("{}", candidate));

        // Public
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Public, one);
        assert_eq!("1i8.public", &format!("{}", candidate));

        // Private
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Private, one);
        assert_eq!("1i8.private", &format!("{}", candidate));
    }

    #[test]
    fn test_display_two() {
        let one = i8::one();
        let two = one + one;

        // Constant
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Constant, two);
        assert_eq!("2i8.constant", &format!("{}", candidate));

        // Public
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Public, two);
        assert_eq!("2i8.public", &format!("{}", candidate));

        // Private
        let candidate = Integer::<CurrentNetwork, i8>::new(Mode::Private, two);
        assert_eq!("2i8.private", &format!("{}", candidate));
    }
}
