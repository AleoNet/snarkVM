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

impl<N: Network> Serialize for Transaction<N> {
    /// Serializes the transaction to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::Deploy(id, owner, deployment, fee) => {
                    let mut transaction = serializer.serialize_struct("Transaction", 5)?;
                    transaction.serialize_field("type", "deploy")?;
                    transaction.serialize_field("id", &id)?;
                    transaction.serialize_field("owner", &owner)?;
                    transaction.serialize_field("deployment", &deployment)?;
                    transaction.serialize_field("fee", &fee)?;
                    transaction.end()
                }
                Self::Execute(id, execution, fee) => {
                    let mut transaction = serializer.serialize_struct("Transaction", 4)?;
                    transaction.serialize_field("type", "execute")?;
                    transaction.serialize_field("id", &id)?;
                    transaction.serialize_field("execution", &execution)?;
                    if let Some(fee) = fee {
                        transaction.serialize_field("fee", &fee)?;
                    }
                    transaction.end()
                }
                Self::Fee(id, fee) => {
                    let mut transaction = serializer.serialize_struct("Transaction", 3)?;
                    transaction.serialize_field("type", "fee")?;
                    transaction.serialize_field("id", &id)?;
                    transaction.serialize_field("fee", &fee)?;
                    transaction.end()
                }
            },
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transaction<N> {
    /// Deserializes the transaction from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Deserialize the transaction into a JSON value.
                let mut transaction = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the transaction ID.
                let id: N::TransactionID = DeserializeExt::take_from_value::<D>(&mut transaction, "id")?;

                // Recover the transaction.
                let transaction = match transaction
                    .get("type")
                    .ok_or_else(|| de::Error::custom("The \"type\" field is missing"))?
                    .as_str()
                {
                    Some("deploy") => {
                        // Retrieve the owner.
                        let owner = DeserializeExt::take_from_value::<D>(&mut transaction, "owner")?;
                        // Retrieve the deployment.
                        let deployment = DeserializeExt::take_from_value::<D>(&mut transaction, "deployment")?;
                        // Retrieve the fee.
                        let fee = DeserializeExt::take_from_value::<D>(&mut transaction, "fee")?;
                        // Construct the transaction.
                        Transaction::from_deployment(owner, deployment, fee).map_err(de::Error::custom)?
                    }
                    Some("execute") => {
                        // Retrieve the execution.
                        let execution = DeserializeExt::take_from_value::<D>(&mut transaction, "execution")?;
                        // Retrieve the fee, if it exists.
                        let fee = serde_json::from_value(
                            transaction.get_mut("fee").unwrap_or(&mut serde_json::Value::Null).take(),
                        )
                        .map_err(de::Error::custom)?;
                        // Construct the transaction.
                        Transaction::from_execution(execution, fee).map_err(de::Error::custom)?
                    }
                    Some("fee") => {
                        // Retrieve the fee.
                        let fee = DeserializeExt::take_from_value::<D>(&mut transaction, "fee")?;
                        // Construct the transaction.
                        Transaction::from_fee(fee).map_err(de::Error::custom)?
                    }
                    _ => return Err(de::Error::custom("Invalid transaction type")),
                };

                // Ensure the transaction ID matches.
                match id == transaction.id() {
                    true => Ok(transaction),
                    false => {
                        Err(error("Mismatching transaction ID, possible data corruption")).map_err(de::Error::custom)
                    }
                }
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transaction"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        let rng = &mut TestRng::default();

        for expected in [
            crate::vm::test_helpers::sample_deployment_transaction(rng),
            crate::vm::test_helpers::sample_execution_transaction_with_fee(rng),
        ]
        .into_iter()
        {
            // Serialize
            let expected_string = &expected.to_string();
            let candidate_string = serde_json::to_string(&expected)?;

            // Deserialize
            assert_eq!(expected, Transaction::from_str(expected_string)?);
            assert_eq!(expected, serde_json::from_str(&candidate_string)?);
        }
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        let rng = &mut TestRng::default();

        for expected in [
            crate::vm::test_helpers::sample_deployment_transaction(rng),
            crate::vm::test_helpers::sample_execution_transaction_with_fee(rng),
        ]
        .into_iter()
        {
            // Serialize
            let expected_bytes = expected.to_bytes_le()?;
            let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
            assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

            // Deserialize
            assert_eq!(expected, Transaction::read_le(&expected_bytes[..])?);
            assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);
        }
        Ok(())
    }
}
