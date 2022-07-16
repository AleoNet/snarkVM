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

use crate::{
    console::{
        network::prelude::*,
        types::{Field, Group},
    },
    vm::VM,
};
use snarkvm_compiler::{Deployment, Execution, Transition};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Transaction<N: Network> {
    /// The transaction deployment publishes an Aleo program to the network.
    Deploy(N::TransactionID, Deployment<N>),
    /// The transaction execution represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>),
}

impl<N: Network> Transaction<N> {
    /// Initializes a new deployment transaction.
    pub fn deploy(deployment: Deployment<N>) -> Result<Self> {
        // Compute the transaction ID.
        let id = N::hash_bhp1024(&deployment.program().to_bytes_le()?.to_bits_le())?.into();
        // Construct the deployment transaction.
        Ok(Self::Deploy(id, deployment))
    }

    /// Initializes a new execution transaction.
    pub fn execute(execution: Execution<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Concatenate the transition IDs as bits.
        let id_bits: Vec<_> = execution.iter().flat_map(|transition| transition.id().to_bits_le()).collect();
        // Compute the transaction ID.
        let id = N::hash_bhp1024(&id_bits)?.into();
        // Construct the execution transaction.
        Ok(Self::Execute(id, execution))
    }

    /// Returns `true` if the transaction is valid.
    pub fn verify(&self) -> bool {
        VM::verify::<N>(self)
    }

    /// Returns the transaction ID.
    pub const fn id(&self) -> N::TransactionID {
        match self {
            Transaction::Deploy(id, ..) => *id,
            Transaction::Execute(id, ..) => *id,
        }
    }

    /// Returns an iterator over the transition IDs, for all executed transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Transaction::Deploy(..) => [].iter().map(Transition::id),
            Transaction::Execute(.., execution) => execution.iter().map(Transition::id),
        }
    }

    /// Returns an iterator over the transition public keys, for all executed transitions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        match self {
            Transaction::Deploy(..) => [].iter().map(Transition::tpk),
            Transaction::Execute(.., execution) => execution.iter().map(Transition::tpk),
        }
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Transaction::Deploy(..) => [].iter().flat_map(Transition::serial_numbers),
            Transaction::Execute(.., execution) => execution.iter().flat_map(Transition::serial_numbers),
        }
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Transaction::Deploy(..) => [].iter().flat_map(Transition::commitments),
            Transaction::Execute(.., execution) => execution.iter().flat_map(Transition::commitments),
        }
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        match self {
            Transaction::Deploy(..) => [].iter().flat_map(Transition::nonces),
            Transaction::Execute(.., execution) => execution.iter().flat_map(Transition::nonces),
        }
    }
}

impl<N: Network> FromStr for Transaction<N> {
    type Err = anyhow::Error;

    /// Initializes the transaction from a JSON-string.
    fn from_str(transaction: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(transaction)?)
    }
}

impl<N: Network> Display for Transaction<N> {
    /// Displays the transaction as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    /// Reads the transaction from the buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the version.
        let version = u16::read_le(&mut reader)?;
        // Ensure the version is valid.
        if version != 0 {
            return Err(error("Invalid transaction version"));
        }

        // Read the variant.
        let variant = u8::read_le(&mut reader)?;
        // Match the variant.
        let transaction = match variant {
            0 => {
                // Read the ID.
                let id = N::TransactionID::read_le(&mut reader)?;
                // Read the deployment.
                let deployment = Deployment::read_le(&mut reader)?;
                // Construct the transaction.
                Transaction::Deploy(id, deployment)
            }
            1 => {
                // Read the ID.
                let id = N::TransactionID::read_le(&mut reader)?;
                // Read the execution.
                let execution = Execution::read_le(&mut reader)?;
                // Construct the transaction.
                Transaction::Execute(id, execution)
            }
            _ => return Err(error("Invalid transaction variant")),
        };
        // Return the transaction.
        Ok(transaction)
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    /// Writes the transaction to the buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the version.
        0u16.write_le(&mut writer)?;

        // Write the transaction.
        match self {
            Self::Deploy(id, deployment) => {
                // Write the variant.
                0u8.write_le(&mut writer)?;
                // Write the ID.
                id.write_le(&mut writer)?;
                // Write the deployment.
                deployment.write_le(&mut writer)
            }
            Self::Execute(id, execution) => {
                // Write the variant.
                1u8.write_le(&mut writer)?;
                // Write the ID.
                id.write_le(&mut writer)?;
                // Write the execution.
                execution.write_le(&mut writer)
            }
        }
    }
}

impl<N: Network> Serialize for Transaction<N> {
    /// Serializes the transaction to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => match self {
                Self::Deploy(id, deployment) => {
                    let mut transaction = serializer.serialize_struct("Transaction", 3)?;
                    transaction.serialize_field("type", "deploy")?;
                    transaction.serialize_field("id", &id)?;
                    transaction.serialize_field("deployment", &deployment)?;
                    transaction.end()
                }
                Self::Execute(id, execution) => {
                    let mut transaction = serializer.serialize_struct("Transaction", 3)?;
                    transaction.serialize_field("type", "execute")?;
                    transaction.serialize_field("id", &id)?;
                    transaction.serialize_field("execution", &execution)?;
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
                let transaction = serde_json::Value::deserialize(deserializer)?;
                // Retrieve the transaction ID.
                let id: N::TransactionID =
                    serde_json::from_value(transaction["id"].clone()).map_err(de::Error::custom)?;

                // Recover the transaction.
                let transaction = match transaction["type"].as_str() {
                    Some("deploy") => {
                        // Retrieve the deployment.
                        let deployment =
                            serde_json::from_value(transaction["deployment"].clone()).map_err(de::Error::custom)?;
                        // Construct the transaction.
                        Transaction::deploy(deployment).map_err(de::Error::custom)?
                    }
                    Some("execute") => {
                        // Retrieve the execution.
                        let execution =
                            serde_json::from_value(transaction["execution"].clone()).map_err(de::Error::custom)?;
                        // Construct the transaction.
                        Transaction::execute(execution).map_err(de::Error::custom)?
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

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::ledger::Block;
//     use console::network::Testnet3;
//
//     type CurrentNetwork = Testnet3;
//     type CurrentAleo = circuit::AleoV0;
//
//     #[test]
//     fn test_serde_json() {
//         let expected = (*Block::<CurrentNetwork>::genesis::<CurrentAleo>().unwrap().transactions())[0].clone();
//
//         // Serialize
//         let expected_string = expected.to_string();
//         let candidate_string = serde_json::to_string(&expected).unwrap();
//         assert_eq!(2670, candidate_string.len(), "Update me if serialization has changed");
//         assert_eq!(expected_string, candidate_string);
//
//         // Deserialize
//         assert_eq!(
//             expected,
//             Transaction::<CurrentNetwork>::from_str(&candidate_string).unwrap()
//         );
//         assert_eq!(expected, serde_json::from_str(&candidate_string).unwrap());
//     }
//
//     #[test]
//     fn test_bincode() {
//         let expected = (*Block::<CurrentNetwork>::genesis::<CurrentAleo>().unwrap().transactions())[0].clone();
//
//         // Serialize
//         let expected_bytes = expected.to_bytes_le().unwrap();
//         let candidate_bytes = bincode::serialize(&expected).unwrap();
//         assert_eq!(1362, expected_bytes.len(), "Update me if serialization has changed");
//         assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);
//
//         // Deserialize
//         assert_eq!(
//             expected,
//             Transaction::<CurrentNetwork>::read_le(&expected_bytes[..]).unwrap()
//         );
//         assert_eq!(expected, bincode::deserialize(&candidate_bytes[..]).unwrap());
//     }
// }
