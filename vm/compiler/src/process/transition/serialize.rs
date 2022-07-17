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

impl<N: Network> Serialize for Transition<N> {
    /// Serializes the transition into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transition = serializer.serialize_struct("Transition", 8)?;
                transition.serialize_field("id", &self.id)?;
                transition.serialize_field("program", &self.program_id)?;
                transition.serialize_field("function", &self.function_name)?;
                transition.serialize_field("inputs", &self.inputs)?;
                transition.serialize_field("outputs", &self.outputs)?;
                transition.serialize_field("proof", &self.proof)?;
                transition.serialize_field("tpk", &self.tpk)?;
                transition.serialize_field("fee", &self.fee)?;
                transition.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transition<N> {
    /// Deserializes the transition from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the transition from a string into a value.
                let transition = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the ID.
                let id: N::TransitionID =
                    serde_json::from_value(transition["id"].clone()).map_err(de::Error::custom)?;

                // Recover the transition.
                let transition = Self::new(
                    // Retrieve the program ID.
                    serde_json::from_value(transition["program"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the function name.
                    serde_json::from_value(transition["function"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the inputs.
                    serde_json::from_value(transition["inputs"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the outputs.
                    serde_json::from_value(transition["outputs"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the proof.
                    serde_json::from_value(transition["proof"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the TPK.
                    serde_json::from_value(transition["tpk"].clone()).map_err(de::Error::custom)?,
                    // Retrieve the fee.
                    serde_json::from_value(transition["fee"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)?;

                // Ensure the transition ID is correct.
                match id == *transition.id() {
                    true => Ok(transition),
                    false => Err(error("Transition ID mismatch, possible data corruption")).map_err(de::Error::custom),
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transition"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // Sample the transition.
        let expected = crate::process::test_helpers::sample_transition();

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, Transition::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // Sample the transition.
        let expected = crate::process::test_helpers::sample_transition();

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, Transition::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
