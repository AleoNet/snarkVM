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

mod string;

use crate::console::{
    collections::merkle_tree::MerklePath,
    network::{prelude::*, BHPMerkleTree},
    types::{Field, Group},
};

use snarkvm_compiler::{Deployment, Execution, Transition};

/// The depth of the Merkle tree for transactions in a block.
const TRANSACTION_DEPTH: u8 = 16;

/// The Merkle tree for transactions in a block.
type TransactionTree<N> = BHPMerkleTree<N, TRANSACTION_DEPTH>;
/// The Merkle path for transaction in a block.
type TransactionPath<N> = MerklePath<N, TRANSACTION_DEPTH>;

#[derive(Clone, PartialEq, Eq)]
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
        let id = *Self::deployment_tree(&deployment)?.root();
        // Construct the deployment transaction.
        Ok(Self::Deploy(id.into(), deployment))
    }

    /// Initializes a new execution transaction.
    pub fn execute(execution: Execution<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Compute the transaction ID.
        let id = *Self::execution_tree(&execution)?.root();
        // Construct the execution transaction.
        Ok(Self::Execute(id.into(), execution))
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

impl<N: Network> Transaction<N> {
    /// Returns the transaction root, by computing the root for a Merkle tree of the transition IDs.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns an inclusion proof for the transaction tree.
    pub fn to_inclusion_proof(&self, index: usize, leaf: impl ToBits) -> Result<TransactionPath<N>> {
        self.to_tree()?.prove(index, &leaf.to_bits_le())
    }

    /// The Merkle tree of transition IDs for the block.
    pub fn to_tree(&self) -> Result<TransactionTree<N>> {
        match self {
            // Compute the deployment tree.
            Transaction::Deploy(_, deployment) => Self::deployment_tree(deployment),
            // Compute the execution tree.
            Transaction::Execute(_, execution) => Self::execution_tree(execution),
        }
    }

    /// Returns the Merkle tree for the given deployment.
    fn deployment_tree(deployment: &Deployment<N>) -> Result<TransactionTree<N>> {
        // Set the variant.
        let variant = 0u8;
        // Retrieve the program.
        let program = deployment.program();
        // Prepare the leaves with the variant, program ID, and function.
        let leaves = program.functions().values().map(|function| {
            Ok(variant
                .to_bits_le()
                .into_iter()
                .chain(program.id().to_bits_le().into_iter())
                .chain(function.to_bytes_le()?.to_bits_le().into_iter())
                .collect())
        });
        // Compute the transactions tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves.collect::<Result<Vec<_>>>()?)
    }

    /// Returns the Merkle tree for the given execution.
    fn execution_tree(execution: &Execution<N>) -> Result<TransactionTree<N>> {
        // Set the variant.
        let variant = 1u8;
        // Prepare the leaves with the variant, program ID, function name, and transition ID.
        let leaves = execution.iter().map(|transition| {
            // Construct the leaf as (variant || program ID || function name || transition ID).
            variant
                .to_bits_le()
                .into_iter()
                .chain(transition.program_id().to_bits_le().into_iter())
                .chain(transition.function_name().to_bits_le().into_iter())
                .chain(transition.id().to_bits_le().into_iter())
                .collect()
        });
        // Compute the transactions tree.
        N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&leaves.collect::<Vec<_>>())
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
        let (id, transaction) = match variant {
            0 => {
                // Read the ID.
                let id = N::TransactionID::read_le(&mut reader)?;
                // Read the deployment.
                let deployment = Deployment::read_le(&mut reader)?;
                // Initialize the transaction.
                let transaction = Self::deploy(deployment).map_err(|e| error(e.to_string()))?;
                // Return the ID and the transaction.
                (id, transaction)
            }
            1 => {
                // Read the ID.
                let id = N::TransactionID::read_le(&mut reader)?;
                // Read the execution.
                let execution = Execution::read_le(&mut reader)?;
                // Initialize the transaction.
                let transaction = Self::execute(execution).map_err(|e| error(e.to_string()))?;
                // Return the ID and the transaction.
                (id, transaction)
            }
            _ => return Err(error("Invalid transaction variant")),
        };

        // Ensure the transaction ID matches.
        match transaction.id() == id {
            // Return the transaction.
            true => Ok(transaction),
            false => Err(error("Transaction ID mismatch")),
        }
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
