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

impl<N: Network> Serialize for Output<N> {
    /// Serializes the transition output into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::Constant(id, value) => {
                    let mut output = serializer.serialize_struct("Output", 3)?;
                    output.serialize_field("type", "constant")?;
                    output.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        output.serialize_field("value", &value)?;
                    }
                    output.end()
                }
                Self::Public(id, value) => {
                    let mut output = serializer.serialize_struct("Output", 3)?;
                    output.serialize_field("type", "public")?;
                    output.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        output.serialize_field("value", &value)?;
                    }
                    output.end()
                }
                Self::Private(id, value) => {
                    let mut output = serializer.serialize_struct("Output", 3)?;
                    output.serialize_field("type", "private")?;
                    output.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        output.serialize_field("value", &value)?;
                    }
                    output.end()
                }
                Self::Record(id, nonce, checksum, value) => {
                    let mut output = serializer.serialize_struct("Output", 5)?;
                    output.serialize_field("type", "record")?;
                    output.serialize_field("id", &id)?;
                    output.serialize_field("nonce", &nonce)?;
                    output.serialize_field("checksum", &checksum)?;
                    if let Some(value) = value {
                        output.serialize_field("value", &value)?;
                    }
                    output.end()
                }
                Self::ExternalRecord(id) => {
                    let mut output = serializer.serialize_struct("Output", 2)?;
                    output.serialize_field("type", "external_record")?;
                    output.serialize_field("id", &id)?;
                    output.end()
                }
            },
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Output<N> {
    /// Deserializes the transition output from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the output from a string into a value.
                let output = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the ID.
                let id: Field<N> = serde_json::from_value(output["id"].clone()).map_err(de::Error::custom)?;

                // Recover the output.
                let output = match output["type"].as_str() {
                    Some("constant") => Output::Constant(id, match output["value"].as_str() {
                        Some(value) => Some(Plaintext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("public") => Output::Public(id, match output["value"].as_str() {
                        Some(value) => Some(Plaintext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("private") => Output::Private(id, match output["value"].as_str() {
                        Some(value) => Some(Ciphertext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("record") => {
                        // Retrieve the nonce.
                        let nonce: Field<N> =
                            serde_json::from_value(output["nonce"].clone()).map_err(de::Error::custom)?;
                        // Retrieve the checksum.
                        let checksum: Field<N> =
                            serde_json::from_value(output["checksum"].clone()).map_err(de::Error::custom)?;
                        // Return the record.
                        Output::Record(id, nonce, checksum, match output["value"].as_str() {
                            Some(value) => {
                                Some(Record::<N, Ciphertext<N>>::from_str(value).map_err(de::Error::custom)?)
                            }
                            None => None,
                        })
                    }
                    Some("external_record") => Output::ExternalRecord(id),
                    _ => return Err(de::Error::custom("Invalid output type")),
                };

                // Ensure the output is well-formed.
                match output.verify() {
                    true => Ok(output),
                    false => Err(error("Transition output verification failed, possible data corruption"))
                        .map_err(de::Error::custom),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transition output"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Add test cases here to be checked for serialization.
    const TEST_CASES: &[&str] = &[
        "{\"type\":\"constant\",\"id\":\"5field\"}",
        "{\"type\":\"public\",\"id\":\"0field\"}",
        "{\"type\":\"private\",\"id\":\"123field\"}",
        "{\"type\":\"record\",\"id\":\"123456789field\", \"nonce\":\"123456789field\", \"checksum\":\"123456789field\"}",
        "{\"type\":\"external_record\",\"id\":\"123456789field\"}",
    ];

    fn check_serde_json<
        T: Serialize + for<'a> Deserialize<'a> + Debug + Display + PartialEq + Eq + FromStr + ToBytes + FromBytes,
    >(
        expected: T,
    ) {
        // Serialize
        let expected_string = expected.to_string();
        let candidate_string = serde_json::to_string(&expected).unwrap();
        let candidate = serde_json::from_str::<T>(&candidate_string).unwrap();
        assert_eq!(expected, candidate);
        assert_eq!(expected_string, candidate_string);
        assert_eq!(expected_string, candidate.to_string());

        // Deserialize
        assert_eq!(expected, T::from_str(&expected_string).unwrap_or_else(|_| panic!("FromStr: {}", expected_string)));
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
        for case in TEST_CASES.iter() {
            check_serde_json(Output::<CurrentNetwork>::from_str(case).unwrap());
        }
    }

    #[test]
    fn test_bincode() {
        for case in TEST_CASES.iter() {
            check_bincode(Output::<CurrentNetwork>::from_str(case).unwrap());
        }
    }
}
