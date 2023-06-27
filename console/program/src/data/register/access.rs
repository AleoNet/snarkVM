// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::Identifier;

use snarkvm_console_network::prelude::*;

/// A register `Access`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Access<N: Network> {
    // TODO (d0cd): Introduce the `Index` variant.
    /// The access is a member.
    Member(Identifier<N>),
}

impl<N: Network> Parser for Access<N> {
    fn parse(string: &str) -> ParserResult<Self>
    where
        Self: Sized,
    {
        alt((map(pair(tag("."), Identifier::parse), |(_, identifier)| Self::Member(identifier)),))(string)
    }
}

impl<N: Network> FromBytes for Access<N> {
    /// Reads the access from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        let variant = u8::read_le(&mut reader)?;
        match variant {
            0 => Ok(Self::Member(Identifier::read_le(&mut reader)?)),
            1.. => Err(error(format!("Failed to deserialize access variant {variant}"))),
        }
    }
}

impl<N: Network> ToBytes for Access<N> {
    /// Write the access to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()>
    where
        Self: Sized,
    {
        match self {
            Access::Member(identifier) => {
                u8::write_le(&0u8, &mut writer)?;
                identifier.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> FromStr for Access<N> {
    type Err = Error;

    /// Parses an identifier into an access.
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

impl<N: Network> Debug for Access<N> {
    /// Prints the access as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for Access<N> {
    /// Prints the access as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the access member, i.e. `.foo`
            Self::Member(identifier) => write!(f, ".{}", identifier),
        }
    }
}

impl<N: Network> Serialize for Access<N> {
    /// Serializes the access into a string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Access<N> {
    /// Deserializes the access from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "access"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::identifier::tests::sample_identifier;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    fn check_bytes(expected: Access<CurrentNetwork>) -> Result<()> {
        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Access::read_le(&expected_bytes[..])?);
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Member
            let identifier = sample_identifier(rng)?;
            check_bytes(Access::Member(identifier))?;
        }
        Ok(())
    }

    #[test]
    fn test_parse() -> Result<()> {
        assert_eq!(Access::parse(".data"), Ok(("", Access::<CurrentNetwork>::Member(Identifier::from_str("data")?))));
        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Must be non-empty.
        assert!(Access::<CurrentNetwork>::parse("").is_err());
        assert!(Access::<CurrentNetwork>::parse(".").is_err());
        assert!(Access::<CurrentNetwork>::parse("[]").is_err());

        // Invalid accesses.
        assert!(Access::<CurrentNetwork>::parse(".0").is_err());
        assert!(Access::<CurrentNetwork>::parse("[index]").is_err());
        assert!(Access::<CurrentNetwork>::parse("[0.0]").is_err());
        assert!(Access::<CurrentNetwork>::parse("[999999999999]").is_err());

        // Must fit within the data capacity of a base field element.
        let access =
            Access::<CurrentNetwork>::parse(".foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(access.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(Access::<CurrentNetwork>::Member(Identifier::from_str("foo")?).to_string(), ".foo");
        Ok(())
    }

    fn check_serde_json<
        T: Serialize + for<'a> Deserialize<'a> + Debug + Display + PartialEq + Eq + FromStr + ToBytes + FromBytes,
    >(
        expected: T,
    ) {
        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected).unwrap();
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());

        // Deserialize
        assert_eq!(expected, T::from_str(expected_string).unwrap_or_else(|_| panic!("FromStr: {expected_string}")));
        assert_eq!(expected, serde_json::from_str(&candidate_string).unwrap());
    }

    fn check_bincode<
        T: Serialize + for<'a> Deserialize<'a> + Debug + Display + PartialEq + Eq + FromStr + ToBytes + FromBytes,
    >(
        expected: T,
    ) {
        // Serialize
        let expected_bytes = expected.to_bytes_le().unwrap();
        let expected_bytes_with_size_encoding = bincode::serialize(&expected).unwrap();
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, T::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..]).unwrap());
    }

    #[test]
    fn test_serde_json() {
        for i in 0..1000 {
            check_serde_json(Access::<CurrentNetwork>::from_str(&format!(".owner_{i}")).unwrap());
        }
    }

    #[test]
    fn test_bincode() {
        for i in 0..1000 {
            check_bincode(Access::<CurrentNetwork>::from_str(&format!(".owner_{i}")).unwrap());
        }
    }
}
