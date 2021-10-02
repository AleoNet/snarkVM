// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::*;
use snarkvm_algorithms::merkle_tree::*;
use snarkvm_dpc::prelude::*;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use parking_lot::RwLock;
use std::{
    fs,
    path::Path,
    sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    },
};

// TODO (howardwu): TEMPORARY - Deprecate this.
pub fn bytes_to_u32(bytes: &[u8]) -> u32 {
    let mut num_bytes = [0u8; 4];
    num_bytes.copy_from_slice(&bytes);

    u32::from_le_bytes(num_bytes)
}

pub type BlockHeight = u32;

pub struct Ledger<N: Network, S: Storage> {
    pub current_block_height: AtomicU32,
    pub commitments_tree: RwLock<MerkleTree<<N as Network>::CommitmentsTreeParameters>>,
    pub serial_numbers_tree: RwLock<MerkleTree<<N as Network>::SerialNumbersTreeParameters>>,
    pub storage: S,
}

impl<N: Network, S: Storage> LedgerScheme<N> for Ledger<N, S> {
    type Block = Block<N>;

    /// Instantiates a new ledger with a genesis block.
    fn new(path: Option<&Path>, genesis_block: Self::Block) -> Result<Self> {
        // Ensure the given block is a genesis block.
        if !genesis_block.header().is_genesis() {
            return Err(LedgerError::InvalidGenesisBlockHeader.into());
        }

        let storage = if let Some(path) = path {
            fs::create_dir_all(&path).map_err(|err| LedgerError::Message(err.to_string()))?;

            S::open(Some(path), None)
        } else {
            S::open(None, None) // this must mean we're using an in-memory storage
        }?;

        if let Some(block_num) = storage.get(COL_META, KEY_BEST_BLOCK_NUMBER.as_bytes())? {
            if bytes_to_u32(&block_num) != 0 {
                return Err(LedgerError::ExistingDatabase.into());
            }
        }

        let leaves: &[[u8; 32]] = &[];
        let commitments_tree = MerkleTree::new(Arc::new(N::commitments_tree_parameters().clone()), leaves)?;
        let serial_numbers_tree = MerkleTree::new(Arc::new(N::serial_numbers_tree_parameters().clone()), leaves)?;

        let ledger = Self {
            current_block_height: Default::default(),
            commitments_tree: RwLock::new(commitments_tree),
            serial_numbers_tree: RwLock::new(serial_numbers_tree),
            storage,
        };

        debug_assert_eq!(ledger.block_height(), 0, "Uninitialized ledger block height must be 0");
        ledger.insert_and_commit(&genesis_block)?;

        Ok(ledger)
    }

    /// Returns the latest number of blocks in the ledger.
    fn block_height(&self) -> u32 {
        self.current_block_height.load(Ordering::SeqCst)
    }

    /// Returns the latest block in the ledger.
    fn latest_block(&self) -> Result<Self::Block> {
        let block_hash = self.get_block_hash(self.block_height())?;
        Ok(self.get_block(&block_hash)?)
    }

    /// Returns the block given the block hash.
    fn get_block(&self, block_hash: &N::BlockHash) -> Result<Self::Block> {
        BlockScheme::from(
            self.get_previous_block_hash(block_hash)?,
            self.get_block_header(block_hash)?,
            self.get_block_transactions(block_hash)?,
        )
    }

    /// Returns the block hash given a block number.
    fn get_block_hash(&self, block_number: BlockHeight) -> Result<N::BlockHash> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_number.to_le_bytes())? {
            Some(block_hash) => Ok(FromBytes::read_le(&block_hash[..])?),
            None => Err(StorageError::MissingBlockHash(block_number).into()),
        }
    }

    /// Returns the block number given a block hash.
    fn get_block_number(&self, block_hash: &N::BlockHash) -> Result<u32> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_hash.to_bytes_le()?)? {
            Some(block_num_bytes) => Ok(bytes_to_u32(&block_num_bytes)),
            None => Err(StorageError::MissingBlockNumber(block_hash.to_string()).into()),
        }
    }

    /// Returns true if the given block hash exists in the ledger.
    fn contains_block_hash(&self, block_hash: &N::BlockHash) -> bool {
        self.get_block_header(block_hash).is_ok()
    }
}

impl<N: Network, S: Storage> Ledger<N, S> {
    /// Return the latest state root of the ledger commitments tree.
    fn latest_digest(&self) -> Result<<N as Network>::CommitmentsRoot> {
        let digest = match self.storage.get(COL_META, KEY_CURR_DIGEST.as_bytes())? {
            Some(current_digest) => current_digest,
            None => to_bytes_le![self.commitments_tree.read().root()]?,
        };
        Ok(FromBytes::read_le(digest.as_slice())?)
    }

    /// Get the previous block hash given the block hash.
    pub fn get_previous_block_hash(&self, block_hash: &N::BlockHash) -> Result<N::BlockHash, StorageError> {
        match self
            .storage
            .get(COL_BLOCK_PREVIOUS_BLOCK_HASH, &block_hash.to_bytes_le()?)?
        {
            Some(previous_block_hash) => Ok(N::BlockHash::read_le(&previous_block_hash[..])?),
            None => Err(StorageError::MissingBlockHeader(block_hash.to_string())),
        }
    }

    /// Get a block header given the block hash.
    pub fn get_block_header(&self, block_hash: &N::BlockHash) -> Result<BlockHeader<N>, StorageError> {
        match self.storage.get(COL_BLOCK_HEADER, &block_hash.to_bytes_le()?)? {
            Some(block_header_bytes) => Ok(BlockHeader::read_le(&block_header_bytes[..])?),
            None => Err(StorageError::MissingBlockHeader(block_hash.to_string())),
        }
    }

    /// Get the list of transaction ids given a block hash.
    pub fn get_block_transactions(&self, block_hash: &N::BlockHash) -> Result<Transactions<N>, StorageError> {
        match self.storage.get(COL_BLOCK_TRANSACTIONS, &block_hash.to_bytes_le()?)? {
            Some(encoded_block_transactions) => Ok(Transactions::read_le(&encoded_block_transactions[..])?),
            None => Err(StorageError::MissingBlockTransactions(block_hash.to_string())),
        }
    }

    /// Get the current commitment index
    fn current_cm_index(&self) -> Result<usize, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_CM_INDEX.as_bytes())? {
            Some(cm_index_bytes) => Ok(bytes_to_u32(&cm_index_bytes) as usize),
            None => Ok(0),
        }
    }

    /// Get the current serial number index
    fn current_sn_index(&self) -> Result<usize, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_SN_INDEX.as_bytes())? {
            Some(sn_index_bytes) => Ok(bytes_to_u32(&sn_index_bytes) as usize),
            None => Ok(0),
        }
    }

    /// Get serial number index.
    fn get_sn_index(&self, sn_bytes: &[u8]) -> Result<Option<usize>, StorageError> {
        match self.storage.get(COL_SERIAL_NUMBER, sn_bytes)? {
            Some(sn_index_bytes) => {
                let mut sn_index = [0u8; 4];
                sn_index.copy_from_slice(&sn_index_bytes[0..4]);

                Ok(Some(u32::from_le_bytes(sn_index) as usize))
            }
            None => Ok(None),
        }
    }

    /// Get commitment index
    fn get_cm_index(&self, cm_bytes: &[u8]) -> Result<Option<usize>, StorageError> {
        match self.storage.get(COL_COMMITMENT, cm_bytes)? {
            Some(cm_index_bytes) => {
                let mut cm_index = [0u8; 4];
                cm_index.copy_from_slice(&cm_index_bytes[0..4]);

                Ok(Some(u32::from_le_bytes(cm_index) as usize))
            }
            None => Ok(None),
        }
    }

    /// Build a new commitment merkle tree from the stored commitments
    pub fn rebuild_commitment_merkle_tree(
        &self,
        additional_cms: Vec<(<N as Network>::Commitment, usize)>,
    ) -> Result<(), StorageError> {
        let mut new_cm_and_indices = additional_cms;

        new_cm_and_indices.sort_by(|&(_, i), &(_, j)| i.cmp(&j));

        let new_commitments: Vec<_> = new_cm_and_indices.into_iter().map(|(cm, _)| cm).collect();

        *self.commitments_tree.write() = self.build_new_commitment_tree(new_commitments)?;

        Ok(())
    }

    /// Build a new commitments tree.
    pub fn build_new_commitment_tree(
        &self,
        additional_cms: Vec<<N as Network>::Commitment>,
    ) -> Result<MerkleTree<<N as Network>::CommitmentsTreeParameters>, StorageError> {
        let current_len = self.storage.get_keys(COL_COMMITMENT)?.len();

        let new_tree = self.commitments_tree.read().rebuild(current_len, &additional_cms)?;

        Ok(new_tree)
    }

    /// Build a new serial numbers tree from the stored serial numbers.
    pub fn rebuild_serial_number_merkle_tree(
        &self,
        additional_sns: Vec<(<N as Network>::SerialNumber, usize)>,
    ) -> Result<(), StorageError> {
        let mut new_sn_and_indices = additional_sns;

        new_sn_and_indices.sort_by(|&(_, i), &(_, j)| i.cmp(&j));

        let new_serial_numbers: Vec<_> = new_sn_and_indices.into_iter().map(|(sn, _)| sn).collect();

        *self.serial_numbers_tree.write() = self.build_new_serial_number_tree(new_serial_numbers)?;

        Ok(())
    }

    /// Build a new serial number merkle tree
    pub fn build_new_serial_number_tree(
        &self,
        additional_sns: Vec<<N as Network>::SerialNumber>,
    ) -> Result<MerkleTree<<N as Network>::SerialNumbersTreeParameters>, StorageError> {
        let current_len = self.storage.get_keys(COL_SERIAL_NUMBER)?.len();

        let new_tree = self.serial_numbers_tree.read().rebuild(current_len, &additional_sns)?;

        Ok(new_tree)
    }

    /// Commit a transaction to the canon chain
    #[allow(clippy::type_complexity)]
    pub(crate) fn commit_transaction(
        &self,
        sn_index: &mut usize,
        cm_index: &mut usize,
        transaction: &Transaction<N>,
    ) -> Result<
        (
            Vec<Op>,
            Vec<(<N as Network>::Commitment, usize)>,
            Vec<(<N as Network>::SerialNumber, usize)>,
        ),
        StorageError,
    > {
        let old_serial_numbers = transaction.serial_numbers();
        let new_commitments = transaction.commitments();

        let mut ops = Vec::with_capacity(old_serial_numbers.len() + new_commitments.len());
        let mut cms = Vec::with_capacity(new_commitments.len());
        let mut sns = Vec::with_capacity(old_serial_numbers.len());

        for sn in old_serial_numbers {
            let sn_bytes = to_bytes_le![sn]?;
            if self.get_sn_index(&sn_bytes)?.is_some() {
                return Err(StorageError::ExistingSn(sn_bytes.to_vec()));
            }

            ops.push(Op::Insert {
                col: COL_SERIAL_NUMBER,
                key: sn_bytes,
                value: (*sn_index as u32).to_le_bytes().to_vec(),
            });
            sns.push((sn.clone(), *sn_index));

            *sn_index += 1;
        }

        for cm in new_commitments {
            let cm_bytes = to_bytes_le![cm]?;
            if self.get_cm_index(&cm_bytes)?.is_some() {
                return Err(StorageError::ExistingCm(cm_bytes.to_vec()));
            }

            ops.push(Op::Insert {
                col: COL_COMMITMENT,
                key: cm_bytes,
                value: (*cm_index as u32).to_le_bytes().to_vec(),
            });
            cms.push((cm.clone(), *cm_index));

            *cm_index += 1;
        }

        Ok((ops, cms, sns))
    }

    /// Insert a block into storage without canonizing/committing it.
    pub fn insert_only(&self, block: &Block<N>) -> Result<(), StorageError> {
        // If the ledger is initialized, ensure the block header is not a genesis header.
        if self.block_height() != 0 && block.header().is_genesis() {
            return Err(StorageError::InvalidBlockHeader);
        }

        // Check that the block does not already exist.
        let block_hash = block.to_block_hash()?;
        if self.contains_block_hash(&block_hash) {
            return Err(BlockError::BlockExists(block_hash.to_string()).into());
        }

        // Ensure there is no conflicting serial number or commitment in the block transactions.
        if !block.transactions().is_valid() {
            return Err(StorageError::ConflictingTransactions);
        }

        let block_hash_bytes = {
            let block_hash_buffer = block_hash.to_bytes_le()?;
            assert_eq!(block_hash_buffer.len(), 32);

            let mut slice = [0u8; 32];
            slice.copy_from_slice(&block_hash_buffer[..]);
            slice
        };

        let mut database_transaction = DatabaseTransaction::new();

        for (index, transaction) in block.transactions().iter().enumerate() {
            let transaction_location = TransactionLocation {
                index: index as u32,
                block_hash: block_hash_bytes,
            };
            database_transaction.push(Op::Insert {
                col: COL_TRANSACTION_LOCATION,
                key: transaction.to_transaction_id()?.to_bytes_le()?,
                value: to_bytes_le![transaction_location]?.to_vec(),
            });
        }

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_PREVIOUS_BLOCK_HASH,
            key: block_hash_bytes.to_vec(),
            value: block.previous_hash().to_bytes_le()?,
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_HEADER,
            key: block_hash_bytes.to_vec(),
            value: to_bytes_le![block.header()]?.to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_TRANSACTIONS,
            key: block_hash_bytes.to_vec(),
            value: to_bytes_le![block.transactions()]?.to_vec(),
        });

        self.storage.batch(database_transaction)?;

        Ok(())
    }

    /// Commit/canonize a particular block.
    pub fn commit(&self, block: &Block<N>) -> Result<(), StorageError> {
        // If the ledger is initialized, ensure the block header is not a genesis header.
        let block_height = self.block_height();
        let is_genesis = block.header().is_genesis();
        if block_height != 0 && is_genesis {
            return Err(StorageError::InvalidBlockHeader);
        }

        // Ensure the block is not already in the canon chain.
        let block_hash = block.to_block_hash()?;
        if self.is_canon(&block_hash) {
            return Err(StorageError::ExistingCanonBlock(block_hash.to_string()));
        }

        // Ensure there is no conflicting serial number or commitment in the block transactions.
        if !block.transactions().is_valid() {
            return Err(StorageError::ConflictingTransactions);
        }

        let mut database_transaction = DatabaseTransaction::new();

        let mut sn_index = self.current_sn_index()?;
        let mut cm_index = self.current_cm_index()?;

        // Process the individual transactions

        let mut transaction_cms = vec![];
        let mut transaction_sns = vec![];

        for transaction in block.transactions().iter() {
            let (tx_ops, cms, sns) = self.commit_transaction(&mut sn_index, &mut cm_index, transaction)?;
            database_transaction.push_vec(tx_ops);
            transaction_cms.extend(cms);
            transaction_sns.extend(sns);
        }

        // Update the database state for current indexes

        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_CURR_SN_INDEX.as_bytes().to_vec(),
            value: (sn_index as u32).to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_CURR_CM_INDEX.as_bytes().to_vec(),
            value: (cm_index as u32).to_le_bytes().to_vec(),
        });

        // Update the best block number.

        let new_block_height = match is_genesis {
            true => block_height,
            false => block_height + 1,
        };

        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_BEST_BLOCK_NUMBER.as_bytes().to_vec(),
            value: new_block_height.to_le_bytes().to_vec(),
        });

        // Update the block location

        let block_hash_bytes = block_hash.to_bytes_le()?;

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: block_hash_bytes.clone(),
            value: new_block_height.to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: new_block_height.to_le_bytes().to_vec(),
            value: block_hash_bytes,
        });

        // If it's the genesis block, store its initial applicable digest.
        if is_genesis {
            database_transaction.push(Op::Insert {
                col: COL_DIGEST,
                key: to_bytes_le![self.latest_digest()?]?,
                value: 0u32.to_le_bytes().to_vec(),
            });
        }

        // Rebuild the new commitment merkle tree
        self.rebuild_commitment_merkle_tree(transaction_cms)?;
        let new_digest = self.commitments_tree.read().root().clone();

        // Rebuild the new serial number merkle tree
        self.rebuild_serial_number_merkle_tree(transaction_sns)?;

        database_transaction.push(Op::Insert {
            col: COL_DIGEST,
            key: to_bytes_le![new_digest]?.to_vec(),
            value: new_block_height.to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_CURR_DIGEST.as_bytes().to_vec(),
            value: to_bytes_le![new_digest]?.to_vec(),
        });

        self.storage.batch(database_transaction)?;

        if !is_genesis {
            self.current_block_height.fetch_add(1, Ordering::SeqCst);
        }

        Ok(())
    }

    /// Insert a block into the storage and commit as part of the longest chain.
    pub fn insert_and_commit(&self, block: &Block<N>) -> Result<(), StorageError> {
        let block_hash = block.to_block_hash()?;

        // If the block does not exist in the storage
        if !self.contains_block_hash(&block_hash) {
            // Insert it first
            self.insert_only(&block)?;
        }
        // Commit it
        self.commit(block)
    }

    /// Returns true if the block exists in the canon chain.
    pub fn is_canon(&self, block_hash: &N::BlockHash) -> bool {
        self.contains_block_hash(block_hash) && self.get_block_number(block_hash).is_ok()
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use snarkvm_dpc::{prelude::*, testnet2::Testnet2};

    #[test]
    fn test_new_ledger_with_genesis_block() {
        let genesis_block = Testnet2::genesis_block();
        let ledger = Ledger::<Testnet2, MemDb>::new(None, genesis_block.clone()).unwrap();
        let genesis_block_hash = ledger.get_block_hash(0).unwrap();

        assert_eq!(ledger.block_height(), 0);
        assert_eq!(ledger.latest_block().unwrap(), genesis_block.clone());
        assert_eq!(ledger.get_block_hash(0).unwrap(), genesis_block_hash.clone());
        assert_eq!(ledger.get_block(&genesis_block_hash).unwrap(), genesis_block.clone());
        assert_eq!(ledger.get_block_number(&genesis_block_hash).unwrap(), 0);
        assert_eq!(ledger.contains_block_hash(&genesis_block_hash), true);

        assert!(ledger.get_block(&Default::default()).is_err());
    }
}
