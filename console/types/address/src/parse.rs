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

static ADDRESS_PREFIX: &str = "aleo";

impl<E: Environment> Parser for Address<E> {
    /// Parses a string into an address.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Prepare a parser for the Aleo address.
        let parse_address = recognize(pair(
            tag("aleo1"),
            many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))),
        ));

        // Parse the address from the string.
        map_res(parse_address, |address: &str| -> Result<_, Error> { Self::from_str(&address.replace('_', "")) })(
            string,
        )
    }
}

impl<E: Environment> FromStr for Address<E> {
    type Err = Error;

    /// Reads in an account address string.
    fn from_str(address: &str) -> Result<Self, Self::Err> {
        // Ensure the address string length is 63 characters.
        if address.len() != 63 {
            bail!("Invalid account address length: found {}, expected 63", address.len())
        }
        // Decode the address string from bech32m.
        let (hrp, data, variant) = bech32::decode(address)?;
        if hrp != ADDRESS_PREFIX {
            bail!("Failed to decode address: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode address: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found an address that is not bech32m encoded: {address}");
        }
        // Decode the address data from u5 to u8, and into an account address.
        Ok(Self::read_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<E: Environment> Debug for Address<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<E: Environment> Display for Address<E> {
    /// Writes an account address as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Convert the address to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string =
            bech32::encode(ADDRESS_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?;
        // Output the string.
        Display::fmt(&string, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 1_000;

    #[test]
    fn test_parse() -> Result<()> {
        // Ensure type and empty value fails.
        assert!(Address::<CurrentEnvironment>::parse(Address::<CurrentEnvironment>::type_name()).is_err());
        assert!(Address::<CurrentEnvironment>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a new address.
            let address = Address::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));

            let expected = format!("{address}");
            let (remainder, candidate) = Address::<CurrentEnvironment>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!(ADDRESS_PREFIX, candidate.to_string().split('1').next().unwrap());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_string() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let expected = Address::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, Address::from_str(&candidate)?);
            assert_eq!(ADDRESS_PREFIX, candidate.to_string().split('1').next().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let expected = Address::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));

            let candidate = expected.to_string();
            assert_eq!(format!("{expected}"), candidate);
            assert_eq!(ADDRESS_PREFIX, candidate.split('1').next().unwrap());

            let candidate_recovered = Address::<CurrentEnvironment>::from_str(&candidate.to_string())?;
            assert_eq!(expected, candidate_recovered);
        }
        Ok(())
    }
}
