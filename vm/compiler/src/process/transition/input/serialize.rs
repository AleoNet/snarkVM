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

impl<N: Network> Serialize for Input<N> {
    /// Serializes the transition input into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::Constant(id, value) => {
                    let mut input = serializer.serialize_struct("Input", 3)?;
                    input.serialize_field("type", "constant")?;
                    input.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        input.serialize_field("value", &value)?;
                    }
                    input.end()
                }
                Self::Public(id, value) => {
                    let mut input = serializer.serialize_struct("Input", 3)?;
                    input.serialize_field("type", "public")?;
                    input.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        input.serialize_field("value", &value)?;
                    }
                    input.end()
                }
                Self::Private(id, value) => {
                    let mut input = serializer.serialize_struct("Input", 3)?;
                    input.serialize_field("type", "private")?;
                    input.serialize_field("id", &id)?;
                    if let Some(value) = value {
                        input.serialize_field("value", &value)?;
                    }
                    input.end()
                }
                Self::Record(id) => {
                    let mut input = serializer.serialize_struct("Input", 2)?;
                    input.serialize_field("type", "record")?;
                    input.serialize_field("id", &id)?;
                    input.end()
                }
                Self::ExternalRecord(id) => {
                    let mut input = serializer.serialize_struct("Input", 2)?;
                    input.serialize_field("type", "external_record")?;
                    input.serialize_field("id", &id)?;
                    input.end()
                }
            },
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Input<N> {
    /// Deserializes the transition input from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the input from a string into a value.
                let input = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the ID.
                let id: Field<N> = serde_json::from_value(input["id"].clone()).map_err(de::Error::custom)?;

                // Recover the input.
                let input = match input["type"].as_str() {
                    Some("constant") => Input::Constant(id, match input["value"].as_str() {
                        Some(value) => Some(Plaintext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("public") => Input::Public(id, match input["value"].as_str() {
                        Some(value) => Some(Plaintext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("private") => Input::Private(id, match input["value"].as_str() {
                        Some(value) => Some(Ciphertext::<N>::from_str(value).map_err(de::Error::custom)?),
                        None => None,
                    }),
                    Some("record") => Input::Record(id),
                    Some("external_record") => Input::ExternalRecord(id),
                    _ => return Err(de::Error::custom("Invalid input type")),
                };

                // Ensure the input is well-formed.
                match input.verify() {
                    true => Ok(input),
                    false => Err(error("Transition input verification failed, possible data corruption"))
                        .map_err(de::Error::custom),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transition input"),
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
        "{\"type\":\"record\",\"id\":\"123456789field\"}",
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
            check_serde_json(Input::<CurrentNetwork>::from_str(case).unwrap());
        }
    }

    #[test]
    fn test_bincode() {
        for case in TEST_CASES.iter() {
            check_bincode(Input::<CurrentNetwork>::from_str(case).unwrap());
        }
    }
}
