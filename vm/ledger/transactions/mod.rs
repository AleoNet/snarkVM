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

mod merkle;
pub use merkle::*;

mod string;

use crate::{
    console::{
        collections::merkle_tree::MerklePath,
        network::{prelude::*, BHPMerkleTree},
        types::{Field, Group},
    },
    ledger::Transaction,
    vm::VM,
};

use indexmap::IndexMap;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Clone, PartialEq, Eq)]
pub struct Transactions<N: Network> {
    /// The transactions included in a block.
    transactions: IndexMap<N::TransactionID, Transaction<N>>,
}

impl<N: Network> Transactions<N> {
    /// Initializes from a given transactions list.
    pub fn from(transactions: &[Transaction<N>]) -> Result<Self> {
        // Construct the transactions.
        let transactions = Self {
            transactions: transactions.iter().cloned().map(|transaction| (transaction.id(), transaction)).collect(),
        };
        // Ensure the transactions are valid.
        match transactions.verify() {
            true => Ok(transactions),
            false => bail!("Failed to initialize a new 'Transactions' instance"),
        }
    }

    /// Returns `true` if the transactions are well-formed.
    pub fn verify(&self) -> bool {
        // Ensure the transactions list is not empty.
        if self.transactions.is_empty() {
            eprintln!("Cannot validate an empty transactions list");
            return false;
        }

        // Ensure each transaction is well-formed.
        if !self.transactions.par_iter().all(|(_, transaction)| VM::verify::<N>(transaction)) {
            eprintln!("Invalid transaction found in the transactions list");
            return false;
        }

        // Ensure there are no duplicate transactions.
        if has_duplicates(self.transaction_ids()) {
            eprintln!("Found duplicate transaction id in the transactions list");
            return false;
        }

        // Ensure there are no duplicate transition public keys.
        if has_duplicates(self.transition_public_keys()) {
            eprintln!("Found duplicate transition public keys in the transactions list");
            return false;
        }

        // Ensure there are no duplicate serial numbers.
        if has_duplicates(self.serial_numbers()) {
            eprintln!("Found duplicate serial numbers in the transactions list");
            return false;
        }

        // Ensure there are no duplicate commitments.
        if has_duplicates(self.commitments()) {
            eprintln!("Found duplicate commitments in the transactions list");
            return false;
        }

        // Ensure there are no duplicate nonces.
        if has_duplicates(self.nonces()) {
            eprintln!("Found duplicate nonces in the transactions list");
            return false;
        }

        // // Ensure there is 1 coinbase transaction.
        // let num_coinbase = self.transactions.iter().filter(|t| t.value_balance().is_negative()).count();
        // if num_coinbase != 1 {
        //     eprintln!("Block must have exactly 1 coinbase transaction, found {}", num_coinbase);
        //     return false;
        // }

        true
    }
}

impl<N: Network> Transactions<N> {
    /// Returns an iterator over all transactions in `self` that are deployments.
    pub fn deployments(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values().filter(|transaction| matches!(transaction, Transaction::Deploy(..)))
    }

    /// Returns an iterator over all transactions in `self` that are executions.
    pub fn executions(&self) -> impl '_ + Iterator<Item = &Transaction<N>> {
        self.transactions.values().filter(|transaction| matches!(transaction, Transaction::Execute(..)))
    }
}

impl<N: Network> Transactions<N> {
    // /// Returns the state roots, by constructing a flattened list of state roots from all transactions.
    // pub fn state_roots(&self) -> impl Iterator<Item = N::LedgerRoot> + '_ {
    //     self.transactions.iter().map(Transaction::state_roots)
    // }

    /// Returns an iterator over the transaction IDs, for all transactions in `self`.
    pub fn transaction_ids(&self) -> impl '_ + Iterator<Item = &N::TransactionID> {
        self.transactions.keys()
    }

    /// Returns an iterator over the transition public keys, for all executed transactions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transactions.values().flat_map(Transaction::transition_public_keys)
    }

    /// Returns an iterator over the serial numbers, for all executed transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transaction::serial_numbers)
    }

    /// Returns an iterator over the commitments, for all executed transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transaction::commitments)
    }

    /// Returns an iterator over the nonces, for all executed transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transactions.values().flat_map(Transaction::nonces)
    }

    // /// Returns the net value balance, by summing the value balance from all transactions.
    // pub fn net_value_balance(&self) -> AleoAmount {
    //     self.transactions.iter().map(Transaction::value_balance).fold(AleoAmount::ZERO, |a, b| a.add(b))
    // }

    // /// Returns the total transaction fees, by summing the value balance from all positive transactions.
    // /// Note - this amount does *not* include the block reward.
    // pub fn transaction_fees(&self) -> AleoAmount {
    //     self.transactions
    //         .iter()
    //         .filter_map(|t| match t.value_balance().is_negative() {
    //             true => None,
    //             false => Some(t.value_balance()),
    //         })
    //         .fold(AleoAmount::ZERO, |a, b| a.add(b))
    // }

    // /// Returns the coinbase transaction for the block.
    // pub fn to_coinbase_transaction(&self) -> Result<Transaction<N>> {
    //     // Filter out all transactions with a positive value balance.
    //     let coinbase_transaction: Vec<_> = self.iter().filter(|t| t.value_balance().is_negative()).collect();
    //
    //     // Ensure there is exactly 1 coinbase transaction.
    //     let num_coinbase = coinbase_transaction.len();
    //     match num_coinbase == 1 {
    //         true => Ok(coinbase_transaction[0].clone()),
    //         false => Err(anyhow!("Block must have 1 coinbase transaction, found {}", num_coinbase)),
    //     }
    // }

    // /// Returns records from the transactions belonging to the given account view key.
    // pub fn to_decrypted_records<'a>(
    //     &'a self,
    //     decryption_key: &'a DecryptionKey<N>,
    // ) -> impl Iterator<Item = Record<N>> + 'a {
    //     self.transactions.iter().flat_map(move |transaction| transaction.to_decrypted_records(decryption_key))
    // }
}

impl<N: Network> FromBytes for Transactions<N> {
    /// Reads the transactions from buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of transactions.
        let num_txs: u16 = FromBytes::read_le(&mut reader)?;
        // Read the transactions.
        let transactions = (0..num_txs).map(|_| FromBytes::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?;
        // Return the transactions.
        Self::from(&transactions).map_err(|e| error(e.to_string()))
    }
}

impl<N: Network> ToBytes for Transactions<N> {
    /// Writes the transactions to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the number of transactions.
        (self.transactions.len() as u16).write_le(&mut writer)?;
        // Write the transactions.
        self.transactions.values().try_for_each(|transaction| transaction.write_le(&mut writer))
    }
}

impl<N: Network> Serialize for Transactions<N> {
    /// Serializes the transactions to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut transactions = serializer.serialize_struct("Transactions", 1)?;
                transactions.serialize_field("transactions", &self.transactions)?;
                transactions.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Transactions<N> {
    /// Deserializes the transactions from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let transactions = serde_json::Value::deserialize(deserializer)?;
                let transactions: Vec<_> =
                    serde_json::from_value(transactions["transactions"].clone()).map_err(de::Error::custom)?;
                Ok(Self::from(&transactions).map_err(de::Error::custom)?)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "transactions"),
        }
    }
}

impl<N: Network> Deref for Transactions<N> {
    type Target = IndexMap<N::TransactionID, Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.transactions
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::ledger::Block;
//
//     use snarkvm::prelude::Testnet3;
//
//     type CurrentNetwork = Testnet3;
//     type A = snarkvm::circuit::AleoV0;
//
//     // TODO (raychu86): Make the genesis block static, so we don't have to regenerate one for every test.
//
//     // #[test]
//     // fn test_to_decrypted_records() {
//     //     let rng = &mut thread_rng();
//     //     let account = Account::<CurrentNetwork>::new(rng);
//     //
//     //     // Craft a transaction with 1 coinbase record.
//     //     let genesis_block = Block::<Testnet2>::genesis();
//     //     let (transaction, expected_record) = Transaction::new_coinbase(account.address(), AleoAmount(1234), true, rng).unwrap();
//     //
//     //     // Craft a Transactions struct with 1 coinbase record.
//     //     let transactions = Transactions::from(&[transaction]).unwrap();
//     //     let decrypted_records = transactions
//     //         .to_decrypted_records(&account.view_key().into())
//     //         .collect::<Vec<Record<CurrentNetwork>>>();
//     //     assert_eq!(decrypted_records.len(), 1); // Excludes dummy records upon decryption.
//     //
//     //     let candidate_record = decrypted_records.first().unwrap();
//     //     assert_eq!(&expected_record, candidate_record);
//     //     assert_eq!(expected_record.owner(), candidate_record.owner());
//     //     assert_eq!(expected_record.value(), candidate_record.value());
//     //     // TODO (howardwu): Reenable this after fixing how payloads are handled.
//     //     // assert_eq!(expected_record.payload(), candidate_record.payload());
//     //     assert_eq!(expected_record.program_id(), candidate_record.program_id());
//     // }
//
//     #[test]
//     fn test_duplicate_transactions() {
//         // Fetch any transaction.
//         let transaction = Block::<CurrentNetwork>::genesis::<A>().unwrap().transactions().transactions[0].clone();
//
//         // Duplicate the transaction, and ensure it is invalid.
//         assert!(Transactions::from(&[transaction.clone(), transaction]).is_err());
//     }
//
//     #[test]
//     fn test_transactions_serde_json() {
//         let expected_transactions = Block::<CurrentNetwork>::genesis::<A>().unwrap().transactions().clone();
//
//         // Serialize
//         let expected_string = expected_transactions.to_string();
//         let candidate_string = serde_json::to_string(&expected_transactions).unwrap();
//         assert_eq!(2689, candidate_string.len(), "Update me if serialization has changed");
//         assert_eq!(expected_string, candidate_string);
//
//         // Deserialize
//         assert_eq!(
//             expected_transactions,
//             Transactions::<CurrentNetwork>::from_str(&candidate_string).unwrap()
//         );
//         assert_eq!(expected_transactions, serde_json::from_str(&candidate_string).unwrap());
//     }
//
//     #[test]
//     fn test_transactions_bincode() {
//         let expected_transactions = Block::<CurrentNetwork>::genesis::<A>().unwrap().transactions().clone();
//
//         // Serialize
//         let expected_bytes = expected_transactions.to_bytes_le().unwrap();
//         let candidate_bytes = bincode::serialize(&expected_transactions).unwrap();
//         assert_eq!(1364, expected_bytes.len(), "Update me if serialization has changed");
//         // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
//         assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);
//
//         // Deserialize
//         assert_eq!(
//             expected_transactions,
//             Transactions::<CurrentNetwork>::read_le(&expected_bytes[..]).unwrap()
//         );
//         assert_eq!(expected_transactions, bincode::deserialize(&candidate_bytes[..]).unwrap());
//     }
// }
