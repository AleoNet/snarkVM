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

impl<N: Network> Parser for Group<N> {
    /// Parses a string into a group circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the group from the string.
        let (string, group): (&str, N::Affine) = map_res(tag(Self::type_name()), |_| {
            let x_coordinate = primitive.replace('_', "").parse()?;
            // Recover and negate the group element if the negative sign was present.
            match negation {
                true => Ok(-N::affine_from_x_coordinate(x_coordinate)?),
                false => N::affine_from_x_coordinate(x_coordinate),
            }
        })(string)?;

        Ok((string, Group::new(group)))
    }
}

impl<N: Network> FromStr for Group<N> {
    type Err = Error;

    /// Parses a string into a group.
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

impl<N: Network> Debug for Group<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Group<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.group.to_affine().to_x_coordinate(), Self::type_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1_000;

    #[test]
    fn test_parse() -> Result<()> {
        let rng = &mut test_rng();

        // Ensure empty value fails.
        assert!(Group::<CurrentNetwork>::parse(&Group::<CurrentNetwork>::type_name()).is_err());
        assert!(Group::<CurrentNetwork>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let group: <CurrentNetwork as Network>::Affine = Uniform::rand(rng);

            let expected = format!("{}{}", group.to_x_coordinate(), Group::<CurrentNetwork>::type_name());
            let (remainder, candidate) = Group::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a group from the given element,
        /// format it in display mode, and recover a group from it.
        fn check_display<N: Network>(element: N::Affine) {
            let candidate = Group::<N>::new(element);
            assert_eq!(format!("{}{}", element.to_x_coordinate(), Group::<N>::type_name()), format!("{candidate}"));

            let candidate_recovered = Group::<N>::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        for _ in 0..ITERATIONS {
            let element = Uniform::rand(&mut test_rng());

            check_display::<CurrentNetwork>(element);
        }
    }

    #[test]
    fn test_display_zero() {
        let zero = <CurrentNetwork as Network>::Affine::zero();

        let candidate = Group::<CurrentNetwork>::new(zero);
        assert_eq!("0group", &format!("{}", candidate));
    }

    // #[test]
    // fn test_display_one() {
    //     let one = <CurrentNetwork as Network>::Affine::prime_subgroup_generator();
    //
    //     let candidate = Group::<CurrentNetwork>::new(one);
    //     assert_eq!("1group", &format!("{}", candidate));
    // }
    //
    // #[test]
    // fn test_display_two() {
    //     let one = <CurrentNetwork as Network>::Projective::prime_subgroup_generator();
    //     let two = (one + one).to_affine();
    //
    //     let candidate = Group::<CurrentNetwork>::new(two);
    //     assert_eq!("2group", &format!("{}", candidate));
    // }
}
