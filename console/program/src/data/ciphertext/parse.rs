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

static CIPHERTEXT_PREFIX: &str = "ciphertext";

impl<N: Network> Parser for Ciphertext<N> {
    /// Parses a string into an ciphertext.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Prepare a parser for the Aleo ciphertext.
        let parse_ciphertext = recognize(pair(
            pair(tag(CIPHERTEXT_PREFIX), tag("1")),
            many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))),
        ));

        // Parse the ciphertext from the string.
        map_res(parse_ciphertext, |ciphertext: &str| -> Result<_, Error> {
            Self::from_str(&ciphertext.replace('_', ""))
        })(string)
    }
}

impl<N: Network> FromStr for Ciphertext<N> {
    type Err = Error;

    /// Reads in the ciphertext string.
    fn from_str(ciphertext: &str) -> Result<Self, Self::Err> {
        // Decode the ciphertext string from bech32m.
        let (hrp, data, variant) = bech32::decode(ciphertext)?;
        if hrp != CIPHERTEXT_PREFIX {
            bail!("Failed to decode ciphertext: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode ciphertext: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found an ciphertext that is not bech32m encoded: {ciphertext}");
        }
        // Decode the ciphertext data from u5 to u8, and into the ciphertext.
        Ok(Self::read_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<N: Network> Debug for Ciphertext<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Ciphertext<N> {
    /// Writes the ciphertext as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Convert the ciphertext to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string =
            bech32::encode(CIPHERTEXT_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?;
        // Output the string.
        Display::fmt(&string, f)
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
        // Ensure type and empty value fails.
        assert!(Ciphertext::<CurrentNetwork>::parse(&format!("{CIPHERTEXT_PREFIX}1")).is_err());
        assert!(Ciphertext::<CurrentNetwork>::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a new ciphertext.
            let ciphertext =
                Ciphertext::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>());

            let expected = format!("{ciphertext}");
            let (remainder, candidate) = Ciphertext::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!(CIPHERTEXT_PREFIX, candidate.to_string().split('1').next().unwrap());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_string() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new ciphertext.
            let expected =
                Ciphertext::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>());

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, Ciphertext::from_str(&candidate)?);
            assert_eq!(CIPHERTEXT_PREFIX, candidate.to_string().split('1').next().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new ciphertext.
            let expected =
                Ciphertext::<CurrentNetwork>((0..100).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>());

            let candidate = expected.to_string();
            assert_eq!(format!("{expected}"), candidate);
            assert_eq!(CIPHERTEXT_PREFIX, candidate.split('1').next().unwrap());

            let candidate_recovered = Ciphertext::<CurrentNetwork>::from_str(&candidate.to_string())?;
            assert_eq!(expected, candidate_recovered);
        }
        Ok(())
    }
}
