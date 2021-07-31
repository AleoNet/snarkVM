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
use snarkvm_utilities::{has_duplicates, to_bytes_le, FromBytes, ToBytes};

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

pub struct Ledger<C: Parameters, S: Storage> {
    pub current_block_height: AtomicU32,
    pub record_commitment_tree: RwLock<MerkleTree<C::RecordCommitmentTreeParameters>>,
    pub record_serial_number_tree: RwLock<MerkleTree<C::RecordSerialNumberTreeParameters>>,
    pub storage: S,
}

impl<C: Parameters, S: Storage> LedgerScheme<C> for Ledger<C, S> {
    type Block = Block<Transaction<C>>;

    /// Instantiates a new ledger with a genesis block.
    fn new(path: Option<&Path>, genesis_block: Self::Block) -> anyhow::Result<Self> {
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
        let record_commitment_tree = MerkleTree::new(Arc::new(C::record_commitment_tree_parameters().clone()), leaves)?;
        let record_serial_number_tree =
            MerkleTree::new(Arc::new(C::record_serial_number_tree_parameters().clone()), leaves)?;

        let ledger = Self {
            current_block_height: Default::default(),
            record_commitment_tree: RwLock::new(record_commitment_tree),
            record_serial_number_tree: RwLock::new(record_serial_number_tree),
            storage,
        };

        debug_assert_eq!(ledger.block_height(), 0, "Uninitialized ledger block height must be 0");
        ledger.insert_and_commit(&genesis_block)?;
        debug_assert_eq!(ledger.block_height(), 1, "Initialized ledger block height must be 1");

        Ok(ledger)
    }

    /// Returns the latest number of blocks in the ledger.
    /// A block height of 0 indicates the ledger is uninitialized.
    /// A block height of 1 indicates the ledger is initialized with a genesis block.
    fn block_height(&self) -> u32 {
        self.current_block_height.load(Ordering::SeqCst)
    }

    /// Returns the latest block in the ledger.
    fn latest_block(&self) -> anyhow::Result<Self::Block> {
        let block_hash = self.get_block_hash(self.block_height())?;
        Ok(self.get_block(&block_hash)?)
    }

    /// Returns the block given the block hash.
    fn get_block(&self, block_hash: &BlockHeaderHash) -> anyhow::Result<Self::Block> {
        Ok(Self::Block {
            header: self.get_block_header(block_hash)?,
            transactions: self.get_block_transactions(block_hash)?,
        })
    }

    /// Returns the block hash given a block number.
    fn get_block_hash(&self, block_number: BlockHeight) -> anyhow::Result<BlockHeaderHash> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_number.to_le_bytes())? {
            Some(block_header_hash) => Ok(BlockHeaderHash::new(block_header_hash)),
            None => Err(StorageError::MissingBlockHash(block_number).into()),
        }
    }

    /// Returns true if the given block hash exists in the ledger.
    fn contains_block_hash(&self, block_hash: &BlockHeaderHash) -> bool {
        self.get_block_header(block_hash).is_ok()
    }
}

impl<C: Parameters, S: Storage> RecordCommitmentTree<C> for Ledger<C, S> {
    /// Return a digest of the latest ledger Merkle tree.
    fn latest_digest(&self) -> Option<MerkleTreeDigest<C::RecordCommitmentTreeParameters>> {
        let digest = match self.storage.get(COL_META, KEY_CURR_DIGEST.as_bytes()).unwrap() {
            Some(current_digest) => current_digest,
            None => to_bytes_le![self.record_commitment_tree.read().root()].unwrap(),
        };
        Some(FromBytes::read_le(digest.as_slice()).unwrap())
    }

    /// Check that st_{ts} is a valid digest for some (past) ledger state.
    fn is_valid_digest(&self, digest: &MerkleTreeDigest<C::RecordCommitmentTreeParameters>) -> bool {
        self.storage.exists(COL_DIGEST, &to_bytes_le![digest].unwrap())
    }

    /// Returns true if the given commitment exists in the ledger.
    fn contains_commitment(&self, commitment: &C::RecordCommitment) -> bool {
        self.storage.exists(COL_COMMITMENT, &commitment.to_bytes_le().unwrap())
    }

    /// Returns the Merkle path to the latest ledger digest
    /// for a given commitment, if it exists in the ledger.
    fn prove_cm(&self, cm: &C::RecordCommitment) -> anyhow::Result<MerklePath<C::RecordCommitmentTreeParameters>> {
        let cm_index = self
            .get_cm_index(&cm.to_bytes_le()?)?
            .ok_or(LedgerError::InvalidCmIndex)?;
        let result = self.record_commitment_tree.read().generate_proof(cm_index, cm)?;

        Ok(result)
    }
}

impl<C: Parameters, S: Storage> RecordSerialNumberTree<C> for Ledger<C, S> {
    /// Returns true if the given serial number exists in the ledger.
    fn contains_serial_number(&self, serial_number: &C::AccountSignaturePublicKey) -> bool {
        self.storage
            .exists(COL_SERIAL_NUMBER, &serial_number.to_bytes_le().unwrap())
    }
}

impl<C: Parameters, S: Storage> Ledger<C, S> {
    /// Find the potential child block hashes given a parent block header.
    pub fn get_child_block_hashes(
        &self,
        parent_header: &BlockHeaderHash,
    ) -> Result<Vec<BlockHeaderHash>, StorageError> {
        match self.storage.get(COL_CHILD_HASHES, &parent_header.0)? {
            Some(encoded_child_block_hashes) => Ok(bincode::deserialize(&encoded_child_block_hashes[..])?),
            None => Ok(vec![]),
        }
    }

    /// Get the block number given a block hash.
    pub fn get_block_number(&self, block_hash: &BlockHeaderHash) -> Result<u32, StorageError> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_hash.0)? {
            Some(block_num_bytes) => Ok(bytes_to_u32(&block_num_bytes)),
            None => Err(StorageError::MissingBlockNumber(block_hash.to_string())),
        }
    }

    /// Get a block header given the block hash.
    pub fn get_block_header(&self, block_hash: &BlockHeaderHash) -> Result<BlockHeader, StorageError> {
        match self.storage.get(COL_BLOCK_HEADER, &block_hash.0)? {
            Some(block_header_bytes) => Ok(BlockHeader::read_le(&block_header_bytes[..])?),
            None => Err(StorageError::MissingBlockHeader(block_hash.to_string())),
        }
    }

    /// Get the list of transaction ids given a block hash.
    pub fn get_block_transactions(
        &self,
        block_hash: &BlockHeaderHash,
    ) -> Result<Transactions<Transaction<C>>, StorageError> {
        match self.storage.get(COL_BLOCK_TRANSACTIONS, &block_hash.0)? {
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
    pub fn rebuild_merkle_tree(
        &self,
        additional_cms: Vec<(<Transaction<C> as TransactionScheme>::Commitment, usize)>,
    ) -> Result<(), StorageError> {
        let mut new_cm_and_indices = additional_cms;

        let current_len = self.storage.get_keys(COL_COMMITMENT)?.len();

        new_cm_and_indices.sort_by(|&(_, i), &(_, j)| i.cmp(&j));

        let new_commitments: Vec<_> = new_cm_and_indices.into_iter().map(|(cm, _)| cm).collect();

        let new_tree = {
            self.record_commitment_tree
                .read()
                .rebuild(current_len, &new_commitments)?
        };
        *self.record_commitment_tree.write() = new_tree;

        Ok(())
    }

    /// Commit a transaction to the canon chain
    #[allow(clippy::type_complexity)]
    pub(crate) fn commit_transaction(
        &self,
        sn_index: &mut usize,
        cm_index: &mut usize,
        transaction: &Transaction<C>,
    ) -> Result<(Vec<Op>, Vec<(<Transaction<C> as TransactionScheme>::Commitment, usize)>), StorageError> {
        let old_serial_numbers = transaction.old_serial_numbers();
        let new_commitments = transaction.new_commitments();

        let mut ops = Vec::with_capacity(old_serial_numbers.len() + new_commitments.len());
        let mut cms = Vec::with_capacity(new_commitments.len());

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

        Ok((ops, cms))
    }

    /// Insert a block into storage without canonizing/committing it.
    pub fn insert_only(&self, block: &Block<Transaction<C>>) -> Result<(), StorageError> {
        // If the ledger is initialized, ensure the block header is not a genesis header.
        if self.block_height() != 0 && block.header().is_genesis() {
            return Err(StorageError::InvalidBlockHeader);
        }

        let block_hash = block.header.get_hash();

        // Check that the block does not already exist.
        if self.contains_block_hash(&block_hash) {
            return Err(BlockError::BlockExists(block_hash.to_string()).into());
        }

        let mut database_transaction = DatabaseTransaction::new();

        let mut transaction_serial_numbers = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_commitments = Vec::with_capacity(block.transactions.0.len());

        for transaction in &block.transactions.0 {
            transaction_serial_numbers.push(transaction.transaction_id()?);
            transaction_commitments.push(transaction.new_commitments());
        }

        // Sanitize the block inputs

        // Check if the transactions in the block have duplicate serial numbers
        if has_duplicates(transaction_serial_numbers) {
            return Err(StorageError::DuplicateSn);
        }

        // Check if the transactions in the block have duplicate commitments
        if has_duplicates(transaction_commitments) {
            return Err(StorageError::DuplicateCm);
        }

        for (index, transaction) in block.transactions.0.iter().enumerate() {
            let transaction_location = TransactionLocation {
                index: index as u32,
                block_hash: block.header.get_hash().0,
            };
            database_transaction.push(Op::Insert {
                col: COL_TRANSACTION_LOCATION,
                key: transaction.transaction_id()?.to_vec(),
                value: to_bytes_le![transaction_location]?.to_vec(),
            });
        }

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_HEADER,
            key: block_hash.0.to_vec(),
            value: to_bytes_le![block.header]?.to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_TRANSACTIONS,
            key: block.header.get_hash().0.to_vec(),
            value: to_bytes_le![block.transactions]?.to_vec(),
        });

        let mut child_hashes = self.get_child_block_hashes(&block.header.previous_block_hash)?;

        if !child_hashes.contains(&block_hash) {
            child_hashes.push(block_hash);

            database_transaction.push(Op::Insert {
                col: COL_CHILD_HASHES,
                key: block.header.previous_block_hash.0.to_vec(),
                value: bincode::serialize(&child_hashes)?,
            });
        }

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_TRANSACTIONS,
            key: block.header.get_hash().0.to_vec(),
            value: to_bytes_le![block.transactions]?.to_vec(),
        });

        self.storage.batch(database_transaction)?;

        Ok(())
    }

    /// Commit/canonize a particular block.
    pub fn commit(&self, block: &Block<Transaction<C>>) -> Result<(), StorageError> {
        // If the ledger is initialized, ensure the block header is not a genesis header.
        if self.block_height() != 0 && block.header().is_genesis() {
            return Err(StorageError::InvalidBlockHeader);
        }

        // Ensure the block is not already in the canon chain.
        let block_header_hash = block.header.get_hash();
        if self.is_canon(&block_header_hash) {
            return Err(StorageError::ExistingCanonBlock(block_header_hash.to_string()));
        }

        let mut database_transaction = DatabaseTransaction::new();

        let mut transaction_serial_numbers = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_commitments = Vec::with_capacity(block.transactions.0.len());

        for transaction in &block.transactions.0 {
            transaction_serial_numbers.push(transaction.transaction_id()?);
            transaction_commitments.push(transaction.new_commitments());
        }

        // Sanitize the block inputs

        // Check if the transactions in the block have duplicate serial numbers
        if has_duplicates(transaction_serial_numbers) {
            return Err(StorageError::DuplicateSn);
        }

        // Check if the transactions in the block have duplicate commitments
        if has_duplicates(transaction_commitments) {
            return Err(StorageError::DuplicateCm);
        }

        let mut sn_index = self.current_sn_index()?;
        let mut cm_index = self.current_cm_index()?;

        // Process the individual transactions

        let mut transaction_cms = vec![];

        for transaction in block.transactions.0.iter() {
            let (tx_ops, cms) = self.commit_transaction(&mut sn_index, &mut cm_index, transaction)?;
            database_transaction.push_vec(tx_ops);
            transaction_cms.extend(cms);
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

        let new_block_height = self.block_height() + 1;

        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_BEST_BLOCK_NUMBER.as_bytes().to_vec(),
            value: new_block_height.to_le_bytes().to_vec(),
        });

        // Update the block location

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: block.header.get_hash().0.to_vec(),
            value: new_block_height.to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: new_block_height.to_le_bytes().to_vec(),
            value: block.header.get_hash().0.to_vec(),
        });

        // Rebuild the new commitment merkle tree
        self.rebuild_merkle_tree(transaction_cms)?;
        let new_digest = self.record_commitment_tree.read().root().clone();

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

        self.current_block_height.fetch_add(1, Ordering::SeqCst);

        Ok(())
    }

    /// Insert a block into the storage and commit as part of the longest chain.
    pub fn insert_and_commit(&self, block: &Block<Transaction<C>>) -> Result<(), StorageError> {
        let block_hash = block.header.get_hash();

        // If the block does not exist in the storage
        if !self.contains_block_hash(&block_hash) {
            // Insert it first
            self.insert_only(&block)?;
        }
        // Commit it
        self.commit(block)
    }

    /// Returns true if the block exists in the canon chain.
    pub fn is_canon(&self, block_hash: &BlockHeaderHash) -> bool {
        self.contains_block_hash(block_hash) && self.get_block_number(block_hash).is_ok()
    }
}
