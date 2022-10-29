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

impl<N: Network> Serialize for TransitionProof<N> {
    /// Serializes the transition proof into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::Birth(execution) => {
                    let mut output = serializer.serialize_struct("TransitionProof", 1)?;
                    output.serialize_field("execution", execution)?;
                    output.end()
                }
                TransitionProof::BirthAndDeath { execution_proof, state_path_proof } => {
                    let mut output = serializer.serialize_struct("TransitionProof", 2)?;
                    output.serialize_field("execution", execution_proof)?;
                    output.serialize_field("state_path", state_path_proof)?;
                    output.end()
                }
            },
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for TransitionProof<N> {
    /// Deserializes the transition proof from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the transition proof from a string into a value.
                let mut proof = serde_json::Value::deserialize(deserializer)?;

                // Retrieve the execution proof.
                let execution: Proof<N> =
                    serde_json::from_value(proof["execution"].take()).map_err(de::Error::custom)?;
                // Retrieve the state path proof (if it exists).
                let state_path: Option<Proof<N>> =
                    serde_json::from_value(proof["state_path"].take()).map_err(de::Error::custom)?;

                // Return the transition proof.
                match state_path {
                    Some(state_path) => Ok(Self::new_birth_and_death(execution, state_path)),
                    None => Ok(Self::new_birth(execution)),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transition proof"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // Sample the transition proof.
        let expected = crate::process::test_helpers::sample_transition().proof().clone();

        check_serde_json(expected);
    }

    #[test]
    fn test_bincode() {
        // Sample the transition proof.
        let expected = crate::process::test_helpers::sample_transition().proof().clone();

        check_bincode(expected);
    }
}
