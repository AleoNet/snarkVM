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

static SIGNATURE_PREFIX: &str = "signature";

impl<N: Network> Parser for Signature<N> {
    /// Parses a string into an signature.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Prepare a parser for the Aleo signature.
        let parse_signature = recognize(pair(
            pair(tag(SIGNATURE_PREFIX), tag("1")),
            many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))),
        ));

        // Parse the signature from the string.
        map_res(parse_signature, |signature: &str| -> Result<_, Error> { Self::from_str(&signature.replace('_', "")) })(
            string,
        )
    }
}

impl<N: Network> FromStr for Signature<N> {
    type Err = Error;

    /// Reads in the signature string.
    fn from_str(signature: &str) -> Result<Self, Self::Err> {
        // Decode the signature string from bech32m.
        let (hrp, data, variant) = bech32::decode(signature)?;
        if hrp != SIGNATURE_PREFIX {
            bail!("Failed to decode signature: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode signature: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found an signature that is not bech32m encoded: {signature}");
        }
        // Decode the signature data from u5 to u8, and into the signature.
        Ok(Self::read_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<N: Network> Debug for Signature<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Signature<N> {
    /// Writes the signature as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Convert the signature to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string =
            bech32::encode(SIGNATURE_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?;
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
        assert!(Signature::<CurrentNetwork>::parse(&format!("{SIGNATURE_PREFIX}1")).is_err());
        assert!(Signature::<CurrentNetwork>::parse("").is_err());

        for i in 0..ITERATIONS {
            // Sample a new signature.
            let expected = test_helpers::sample_signature(i);

            let expected = format!("{expected}");
            let (remainder, candidate) = Signature::<CurrentNetwork>::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!(SIGNATURE_PREFIX, candidate.to_string().split('1').next().unwrap());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_string() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a new signature.
            let expected = test_helpers::sample_signature(i);

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, Signature::from_str(&candidate)?);
            assert_eq!(SIGNATURE_PREFIX, candidate.to_string().split('1').next().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a new signature.
            let expected = test_helpers::sample_signature(i);

            let candidate = expected.to_string();
            assert_eq!(format!("{expected}"), candidate);
            assert_eq!(SIGNATURE_PREFIX, candidate.split('1').next().unwrap());

            let candidate_recovered = Signature::<CurrentNetwork>::from_str(&candidate.to_string())?;
            assert_eq!(expected, candidate_recovered);
        }
        Ok(())
    }
}
