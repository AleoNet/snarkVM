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

static VERIFYING_KEY: &str = "verifier";

impl<N: Network> Parser for VerifyingKey<N> {
    /// Parses a string into the verifying key.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Prepare a parser for the Aleo verifying key.
        let parse_key = recognize(pair(
            pair(tag(VERIFYING_KEY), tag("1")),
            many1(terminated(one_of("qpzry9x8gf2tvdw0s3jn54khce6mua7l"), many0(char('_')))),
        ));

        // Parse the verifying key from the string.
        map_res(parse_key, |key: &str| -> Result<_, Error> { Self::from_str(&key.replace('_', "")) })(string)
    }
}

impl<N: Network> FromStr for VerifyingKey<N> {
    type Err = Error;

    /// Reads in the verifying key string.
    fn from_str(key: &str) -> Result<Self, Self::Err> {
        // Decode the verifying key string from bech32m.
        let (hrp, data, variant) = bech32::decode(key)?;
        if hrp != VERIFYING_KEY {
            bail!("Failed to decode verifying key: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode verifying key: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found a verifying key that is not bech32m encoded: {key}");
        }
        // Decode the verifying key data from u5 to u8, and into the verifying key.
        Ok(Self::read_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<N: Network> Debug for VerifyingKey<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for VerifyingKey<N> {
    /// Writes the verifying key as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Convert the verifying key to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string =
            bech32::encode(VERIFYING_KEY, bytes.to_base32(), bech32::Variant::Bech32m).map_err(|_| fmt::Error)?;
        // Output the string.
        Display::fmt(&string, f)
    }
}
