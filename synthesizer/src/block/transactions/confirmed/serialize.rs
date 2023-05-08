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

impl<N: Network> Serialize for ConfirmedTransaction<N> {
    /// Serializes the confirmed transaction into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::AcceptedDeploy(index, transaction, finalize_operations) => {
                    let mut object = serializer.serialize_struct("ConfirmedTransaction", 5)?;
                    object.serialize_field("status", "accepted")?;
                    object.serialize_field("type", "deploy")?;
                    object.serialize_field("index", index)?;
                    object.serialize_field("transaction", transaction)?;
                    object.serialize_field("finalize", finalize_operations)?;
                    object.end()
                }
                Self::AcceptedExecute(index, transaction, finalize_operations) => {
                    let mut object = serializer.serialize_struct("ConfirmedTransaction", 5)?;
                    object.serialize_field("status", "accepted")?;
                    object.serialize_field("type", "execute")?;
                    object.serialize_field("index", index)?;
                    object.serialize_field("transaction", transaction)?;
                    object.serialize_field("finalize", finalize_operations)?;
                    object.end()
                }
                Self::RejectedDeploy(index, transaction, rejected_deployment) => {
                    let mut object = serializer.serialize_struct("ConfirmedTransaction", 5)?;
                    object.serialize_field("status", "rejected")?;
                    object.serialize_field("type", "deploy")?;
                    object.serialize_field("index", index)?;
                    object.serialize_field("transaction", transaction)?;
                    object.serialize_field("rejected", &rejected_deployment.0)?;
                    object.end()
                }
                Self::RejectedExecute(index, transaction, rejected_execution) => {
                    let mut object = serializer.serialize_struct("ConfirmedTransaction", 5)?;
                    object.serialize_field("status", "rejected")?;
                    object.serialize_field("type", "execute")?;
                    object.serialize_field("index", index)?;
                    object.serialize_field("transaction", transaction)?;
                    object.serialize_field("rejected", &rejected_execution.0)?;
                    object.end()
                }
            },
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ConfirmedTransaction<N> {
    /// Deserializes the confirmed transaction from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the confirmed transaction from a string into a value.
                let mut object = serde_json::Value::deserialize(deserializer)?;

                // Parse the index.
                let index: u32 = DeserializeExt::take_from_value::<D>(&mut object, "index")?;
                // Parse the transaction.
                let transaction: Transaction<N> = DeserializeExt::take_from_value::<D>(&mut object, "transaction")?;

                // Parse the status and type.
                let status = object.get("status").and_then(|t| t.as_str());
                let type_ = object.get("type").and_then(|t| t.as_str());

                // Recover the confirmed transaction.
                match (status, type_) {
                    (Some("accepted"), Some("deploy")) => {
                        // Parse the finalize operations.
                        let finalize: Vec<_> = DeserializeExt::take_from_value::<D>(&mut object, "finalize")?;
                        // Return the accepted deploy transaction.
                        Self::accepted_deploy(index, transaction, finalize).map_err(de::Error::custom)
                    }
                    (Some("accepted"), Some("execute")) => {
                        // Parse the finalize operations.
                        let finalize: Vec<_> = DeserializeExt::take_from_value::<D>(&mut object, "finalize")?;
                        // Return the accepted execute transaction.
                        Self::accepted_execute(index, transaction, finalize).map_err(de::Error::custom)
                    }
                    (Some("rejected"), Some("deploy")) => {
                        // Parse the rejected deployment.
                        let rejected: Deployment<N> = DeserializeExt::take_from_value::<D>(&mut object, "rejected")?;
                        // Return the rejected deploy transaction.
                        Self::rejected_deploy(index, transaction, rejected).map_err(de::Error::custom)
                    }
                    (Some("rejected"), Some("execute")) => {
                        // Parse the rejected execution.
                        let rejected: Execution<N> = DeserializeExt::take_from_value::<D>(&mut object, "rejected")?;
                        // Return the rejected execute transaction.
                        Self::rejected_execute(index, transaction, rejected).map_err(de::Error::custom)
                    }
                    _ => Err(de::Error::custom("Invalid confirmed transaction type")),
                }
            }
            false => {
                FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "confirmed transaction")
            }
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
        assert_eq!(expected, T::from_str(&expected_string).unwrap_or_else(|_| panic!("FromStr: {expected_string}")));
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
        for transaction in crate::block::transactions::confirmed::test_helpers::sample_confirmed_transactions() {
            check_serde_json(transaction);
        }
    }

    #[test]
    fn test_bincode() {
        for transaction in crate::block::transactions::confirmed::test_helpers::sample_confirmed_transactions() {
            check_bincode(transaction);
        }
    }
}
