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

impl<N: Network> Transactions<N> {
    /// Returns the transactions root, by computing the root for a Merkle tree of the transaction IDs.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle path for the transactions leaf.
    pub fn to_path(&self, transaction_id: N::TransactionID) -> Result<TransactionsPath<N>> {
        match self.transactions.get_index_of(&transaction_id) {
            Some(transaction_index) => self.to_tree()?.prove(transaction_index, &transaction_id.to_bits_le()),
            None => bail!("The transaction '{transaction_id}' is not in the block transactions"),
        }
    }

    /// The Merkle tree of transaction IDs for the block.
    pub fn to_tree(&self) -> Result<TransactionsTree<N>> {
        Self::transactions_tree(&self.transactions)
    }

    /// Returns the Merkle tree for the given transactions.
    fn transactions_tree(
        transactions: &IndexMap<N::TransactionID, ConfirmedTransaction<N>>,
    ) -> Result<TransactionsTree<N>> {
        // Ensure the number of transactions is within the allowed range.
        ensure!(
            transactions.len() <= Self::MAX_TRANSACTIONS,
            "Block cannot exceed {} transactions, found {}",
            Self::MAX_TRANSACTIONS,
            transactions.len()
        );
        // Prepare the leaves.
        let leaves = transactions.values().map(|transaction| transaction.id().to_bits_le());
        // Compute the transactions tree.
        N::merkle_tree_bhp::<TRANSACTIONS_DEPTH>(&leaves.collect::<Vec<_>>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_transactions_depth() {
        // Ensure the log2 relationship between depth and the maximum number of transactions.
        assert_eq!(2usize.pow(TRANSACTIONS_DEPTH as u32), Transactions::<CurrentNetwork>::MAX_TRANSACTIONS);
    }
}
