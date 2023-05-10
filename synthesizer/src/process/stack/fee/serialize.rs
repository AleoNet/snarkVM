// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use snarkvm_utilities::DeserializeExt;

impl<N: Network> Serialize for Fee<N> {
    /// Serializes the fee into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut fee = serializer.serialize_struct("Fee", 3)?;
                fee.serialize_field("transition", &self.transition)?;
                fee.serialize_field("global_state_root", &self.global_state_root)?;
                if let Some(inclusion_proof) = &self.inclusion_proof {
                    fee.serialize_field("inclusion", inclusion_proof)?;
                }
                fee.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Fee<N> {
    /// Deserializes the fee from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the fee from a string into a value.
                let mut fee = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the transitions.
                let transition = DeserializeExt::take_from_value::<D>(&mut fee, "transition")?;
                // Retrieve the global state root.
                let global_state_root = DeserializeExt::take_from_value::<D>(&mut fee, "global_state_root")?;
                // Retrieve the inclusion proof.
                let inclusion_proof = DeserializeExt::take_from_value::<D>(&mut fee, "inclusion")?;
                // Recover the fee.
                Ok(Self::from(transition, global_state_root, inclusion_proof))
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "fee"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        let rng = &mut TestRng::default();

        // Sample the fee.
        let expected = crate::vm::test_helpers::sample_fee(rng);

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, Fee::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let rng = &mut TestRng::default();

        // Sample the fee.
        let expected = crate::vm::test_helpers::sample_fee(rng);

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, Fee::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
