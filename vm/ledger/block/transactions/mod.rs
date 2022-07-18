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

mod bytes;
mod serialize;
mod string;

use crate::{
    console::{
        collections::merkle_tree::MerklePath,
        network::{prelude::*, BHPMerkleTree},
        types::{Field, Group},
    },
    ledger::{vm::VM, Transaction},
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
    /// The maximum number of transactions allowed in a block.
    const MAX_TRANSACTIONS: usize = usize::pow(2, TRANSACTIONS_DEPTH as u32);

    /// Initializes from a given transactions list.
    pub fn from(transactions: &[Transaction<N>]) -> Result<Self> {
        // Construct the transactions.
        let transactions = Self {
            transactions: transactions.iter().cloned().map(|transaction| (transaction.id(), transaction)).collect(),
        };
        // Return the transactions.
        Ok(transactions)
    }

    /// Returns `true` if the transactions are well-formed.
    pub fn verify(&self, vm: &VM<N>) -> bool {
        // Ensure the transactions list is not empty.
        if self.transactions.is_empty() {
            eprintln!("Cannot validate an empty transactions list");
            return false;
        }

        // Ensure the number of transactions is within the allowed range.
        if self.transactions.len() > Self::MAX_TRANSACTIONS {
            eprintln!("Cannot validate a transactions list with more than {} transactions", Self::MAX_TRANSACTIONS);
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

        // Ensure each transaction is well-formed.
        if !self.transactions.par_iter().all(|(_, transaction)| transaction.verify(vm)) {
            eprintln!("Invalid transaction found in the transactions list");
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

    // /// Returns records from the transactions belonging to the given account view key.
    // pub fn to_decrypted_records<'a>(
    //     &'a self,
    //     decryption_key: &'a DecryptionKey<N>,
    // ) -> impl Iterator<Item = Record<N>> + 'a {
    //     self.transactions.iter().flat_map(move |transaction| transaction.to_decrypted_records(decryption_key))
    // }
}

impl<N: Network> Deref for Transactions<N> {
    type Target = IndexMap<N::TransactionID, Transaction<N>>;

    fn deref(&self) -> &Self::Target {
        &self.transactions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_duplicate_transactions() {
        // Retrieve the VM.
        let vm = crate::ledger::vm::test_helpers::sample_vm();
        // Retrieve a transaction.
        let transaction = crate::ledger::vm::test_helpers::sample_execution_transaction();
        // Duplicate the transaction.
        let transactions = Transactions::from(&[transaction.clone(), transaction]).unwrap();
        // Ensure the `Transactions` struct only has one instance of the transaction.
        assert_eq!(transactions.len(), 1);
        assert!(!has_duplicates(transactions.transaction_ids()));
        assert!(transactions.verify(&vm));
    }

    // #[test]
    // fn test_to_decrypted_records() {
    //     let rng = &mut thread_rng();
    //     let account = Account::<CurrentNetwork>::new(rng);
    //
    //     // Craft a transaction with 1 coinbase record.
    //     let genesis_block = Block::<Testnet2>::genesis();
    //     let (transaction, expected_record) = Transaction::new_coinbase(account.address(), AleoAmount(1234), true, rng).unwrap();
    //
    //     // Craft a Transactions struct with 1 coinbase record.
    //     let transactions = Transactions::from(&[transaction]).unwrap();
    //     let decrypted_records = transactions
    //         .to_decrypted_records(&account.view_key().into())
    //         .collect::<Vec<Record<CurrentNetwork>>>();
    //     assert_eq!(decrypted_records.len(), 1); // Excludes dummy records upon decryption.
    //
    //     let candidate_record = decrypted_records.first().unwrap();
    //     assert_eq!(&expected_record, candidate_record);
    //     assert_eq!(expected_record.owner(), candidate_record.owner());
    //     assert_eq!(expected_record.value(), candidate_record.value());
    //     // assert_eq!(expected_record.payload(), candidate_record.payload());
    //     assert_eq!(expected_record.program_id(), candidate_record.program_id());
    // }
}
