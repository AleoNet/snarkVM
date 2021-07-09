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
use snarkvm_algorithms::{merkle_tree::*, traits::LoadableMerkleParameters};
use snarkvm_dpc::prelude::*;
use snarkvm_utilities::{has_duplicates, to_bytes, FromBytes, ToBytes};

use parking_lot::RwLock;
use std::{
    collections::HashSet,
    fs,
    marker::PhantomData,
    path::Path,
    sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    },
};

pub type BlockHeight = u32;

pub struct Ledger<T: TransactionScheme, P: LoadableMerkleParameters, S: Storage> {
    pub current_block_height: AtomicU32,
    pub ledger_parameters: Arc<P>,
    pub cm_merkle_tree: RwLock<MerkleTree<P>>,
    pub storage: S,
    pub _transaction: PhantomData<T>,
}

impl<T: TransactionScheme, P: LoadableMerkleParameters, S: Storage> Ledger<T, P, S> {
    /// Returns true if there are no blocks in the ledger.
    pub fn is_empty(&self) -> bool {
        self.get_latest_block().is_err()
    }

    /// Get the latest block in the chain.
    pub fn get_latest_block(&self) -> Result<Block<T>, StorageError> {
        self.get_block_from_block_number(self.get_current_block_height())
    }

    /// Get a block given the block hash.
    pub fn get_block(&self, block_hash: &BlockHeaderHash) -> Result<Block<T>, StorageError> {
        Ok(Block {
            header: self.get_block_header(block_hash)?,
            transactions: self.get_block_transactions(block_hash)?,
        })
    }

    /// Get a block given the block number.
    pub fn get_block_from_block_number(&self, block_number: u32) -> Result<Block<T>, StorageError> {
        if block_number > self.get_current_block_height() {
            return Err(StorageError::BlockError(BlockError::InvalidBlockNumber(block_number)));
        }

        let block_hash = self.get_block_hash(block_number)?;

        self.get_block(&block_hash)
    }

    /// Get the block hash given a block number.
    pub fn get_block_hash(&self, block_number: u32) -> Result<BlockHeaderHash, StorageError> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_number.to_le_bytes())? {
            Some(block_header_hash) => Ok(BlockHeaderHash::new(block_header_hash)),
            None => Err(StorageError::MissingBlockHash(block_number)),
        }
    }

    /// Get the list of transaction ids given a block hash.
    pub fn get_block_transactions(&self, block_hash: &BlockHeaderHash) -> Result<Transactions<T>, StorageError> {
        match self.storage.get(COL_BLOCK_TRANSACTIONS, &block_hash.0)? {
            Some(encoded_block_transactions) => Ok(Transactions::read_le(&encoded_block_transactions[..])?),
            None => Err(StorageError::MissingBlockTransactions(block_hash.to_string())),
        }
    }

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

    /// Get the latest block height of the chain.
    pub fn get_current_block_height(&self) -> BlockHeight {
        self.current_block_height.load(Ordering::SeqCst)
    }

    /// Get the block number given a block hash.
    pub fn get_block_number(&self, block_hash: &BlockHeaderHash) -> Result<u32, StorageError> {
        match self.storage.get(COL_BLOCK_LOCATOR, &block_hash.0)? {
            Some(block_num_bytes) => Ok(bytes_to_u32(&block_num_bytes)),
            None => Err(StorageError::MissingBlockNumber(block_hash.to_string())),
        }
    }

    /// Returns true if the block for the given block header hash exists.
    pub fn block_hash_exists(&self, block_hash: &BlockHeaderHash) -> bool {
        if self.is_empty() {
            return false;
        }

        self.get_block_header(block_hash).is_ok()
    }

    /// Get a block header given the block hash.
    pub fn get_block_header(&self, block_hash: &BlockHeaderHash) -> Result<BlockHeader, StorageError> {
        match self.storage.get(COL_BLOCK_HEADER, &block_hash.0)? {
            Some(block_header_bytes) => Ok(BlockHeader::read_le(&block_header_bytes[..])?),
            None => Err(StorageError::MissingBlockHeader(block_hash.to_string())),
        }
    }

    /// Get the current commitment index
    pub fn current_cm_index(&self) -> Result<usize, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_CM_INDEX.as_bytes())? {
            Some(cm_index_bytes) => Ok(bytes_to_u32(&cm_index_bytes) as usize),
            None => Ok(0),
        }
    }

    /// Get the current serial number index
    pub fn current_sn_index(&self) -> Result<usize, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_SN_INDEX.as_bytes())? {
            Some(sn_index_bytes) => Ok(bytes_to_u32(&sn_index_bytes) as usize),
            None => Ok(0),
        }
    }

    /// Get the current memo index
    pub fn current_memo_index(&self) -> Result<usize, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_MEMO_INDEX.as_bytes())? {
            Some(memo_index_bytes) => Ok(bytes_to_u32(&memo_index_bytes) as usize),
            None => Ok(0),
        }
    }

    /// Get the current ledger digest
    pub fn current_digest(&self) -> Result<Vec<u8>, StorageError> {
        match self.storage.get(COL_META, KEY_CURR_DIGEST.as_bytes())? {
            Some(current_digest) => Ok(current_digest),
            None => Ok(to_bytes![self.cm_merkle_tree.read().root()].unwrap()),
        }
    }

    /// Get the set of past ledger digests
    pub fn past_digests(&self) -> Result<HashSet<Box<[u8]>>, StorageError> {
        let keys = self.storage.get_keys(COL_DIGEST)?;
        let digests = keys.into_iter().collect();

        Ok(digests)
    }

    /// Get serial number index.
    pub fn get_sn_index(&self, sn_bytes: &[u8]) -> Result<Option<usize>, StorageError> {
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
    pub fn get_cm_index(&self, cm_bytes: &[u8]) -> Result<Option<usize>, StorageError> {
        match self.storage.get(COL_COMMITMENT, cm_bytes)? {
            Some(cm_index_bytes) => {
                let mut cm_index = [0u8; 4];
                cm_index.copy_from_slice(&cm_index_bytes[0..4]);

                Ok(Some(u32::from_le_bytes(cm_index) as usize))
            }
            None => Ok(None),
        }
    }

    /// Get memo index
    pub fn get_memo_index(&self, memo_bytes: &[u8]) -> Result<Option<usize>, StorageError> {
        match self.storage.get(COL_MEMO, memo_bytes)? {
            Some(memo_index_bytes) => {
                let mut memo_index = [0u8; 4];
                memo_index.copy_from_slice(&memo_index_bytes[0..4]);

                Ok(Some(u32::from_le_bytes(memo_index) as usize))
            }
            None => Ok(None),
        }
    }

    /// Build a new commitment merkle tree from the stored commitments
    pub fn rebuild_merkle_tree(&self, additional_cms: Vec<(T::Commitment, usize)>) -> Result<(), StorageError> {
        let mut new_cm_and_indices = additional_cms;

        let mut old_cm_and_indices = vec![];
        for (commitment_key, index_value) in self.storage.get_col(COL_COMMITMENT)? {
            let commitment: T::Commitment = FromBytes::read_le(&commitment_key[..])?;
            let index = bytes_to_u32(&index_value) as usize;

            old_cm_and_indices.push((commitment, index));
        }

        old_cm_and_indices.sort_by(|&(_, i), &(_, j)| i.cmp(&j));
        new_cm_and_indices.sort_by(|&(_, i), &(_, j)| i.cmp(&j));

        let old_commitments = old_cm_and_indices.into_iter().map(|(cm, _)| cm);
        let new_commitments: Vec<_> = new_cm_and_indices.into_iter().map(|(cm, _)| cm).collect();

        let new_tree = { self.cm_merkle_tree.read().rebuild(old_commitments, &new_commitments)? };
        *self.cm_merkle_tree.write() = new_tree;

        Ok(())
    }
}

impl<T: TransactionScheme, P: LoadableMerkleParameters, S: Storage> LedgerScheme for Ledger<T, P, S> {
    type Block = Block<Self::Transaction>;
    type Commitment = T::Commitment;
    type MerkleParameters = P;
    type MerklePath = MerklePath<Self::MerkleParameters>;
    type MerkleTreeDigest = MerkleTreeDigest<Self::MerkleParameters>;
    type SerialNumber = T::SerialNumber;
    type Transaction = T;

    /// Instantiates a new ledger with a genesis block.
    fn new(
        path: Option<&Path>,
        parameters: Arc<Self::MerkleParameters>,
        genesis_block: Self::Block,
    ) -> anyhow::Result<Self> {
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
        let empty_cm_merkle_tree = MerkleTree::<Self::MerkleParameters>::new(parameters.clone(), leaves)?;

        let ledger_storage = Self {
            current_block_height: Default::default(),
            storage,
            cm_merkle_tree: RwLock::new(empty_cm_merkle_tree),
            ledger_parameters: parameters,
            _transaction: PhantomData,
        };

        ledger_storage.insert_and_commit(&genesis_block)?;

        Ok(ledger_storage)
    }

    /// Returns the number of blocks including the genesis block
    fn len(&self) -> usize {
        self.get_current_block_height() as usize + 1
    }

    /// Return the parameters used to construct the ledger Merkle tree.
    fn parameters(&self) -> &Arc<Self::MerkleParameters> {
        &self.ledger_parameters
    }

    /// Return a digest of the latest ledger Merkle tree.
    fn digest(&self) -> Option<Self::MerkleTreeDigest> {
        let digest: Self::MerkleTreeDigest = FromBytes::read_le(&self.current_digest().unwrap()[..]).unwrap();
        Some(digest)
    }

    /// Check that st_{ts} is a valid digest for some (past) ledger state.
    fn validate_digest(&self, digest: &Self::MerkleTreeDigest) -> bool {
        self.storage.exists(COL_DIGEST, &to_bytes![digest].unwrap())
    }

    /// Returns true if the given commitment exists in the ledger.
    fn contains_cm(&self, cm: &Self::Commitment) -> bool {
        self.storage.exists(COL_COMMITMENT, &to_bytes![cm].unwrap())
    }

    /// Returns true if the given serial number exists in the ledger.
    fn contains_sn(&self, sn: &Self::SerialNumber) -> bool {
        self.storage.exists(COL_SERIAL_NUMBER, &to_bytes![sn].unwrap())
    }

    /// Returns true if the given memo exists in the ledger.
    fn contains_memo(&self, memo: &<Self::Transaction as TransactionScheme>::Memorandum) -> bool {
        self.storage.exists(COL_MEMO, &to_bytes![memo].unwrap())
    }

    /// Returns the Merkle path to the latest ledger digest
    /// for a given commitment, if it exists in the ledger.
    fn prove_cm(&self, cm: &Self::Commitment) -> anyhow::Result<Self::MerklePath> {
        let cm_index = self.get_cm_index(&to_bytes![cm]?)?.ok_or(LedgerError::InvalidCmIndex)?;
        let result = self.cm_merkle_tree.read().generate_proof(cm_index, cm)?;

        Ok(result)
    }

    /// Returns true if the given Merkle path is a valid witness for
    /// the given ledger digest and commitment.
    fn verify_cm(
        _parameters: &Arc<Self::MerkleParameters>,
        digest: &Self::MerkleTreeDigest,
        cm: &Self::Commitment,
        witness: &Self::MerklePath,
    ) -> bool {
        witness.verify(&digest, cm).unwrap()
    }
}

impl<T: TransactionScheme, P: LoadableMerkleParameters, S: Storage> Ledger<T, P, S> {
    /// Commit a transaction to the canon chain
    #[allow(clippy::type_complexity)]
    pub(crate) fn commit_transaction(
        &self,
        sn_index: &mut usize,
        cm_index: &mut usize,
        memo_index: &mut usize,
        transaction: &T,
    ) -> Result<(Vec<Op>, Vec<(T::Commitment, usize)>), StorageError> {
        let old_serial_numbers = transaction.old_serial_numbers();
        let new_commitments = transaction.new_commitments();

        let mut ops = Vec::with_capacity(old_serial_numbers.len() + new_commitments.len());
        let mut cms = Vec::with_capacity(new_commitments.len());

        for sn in old_serial_numbers {
            let sn_bytes = to_bytes![sn]?;
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
            let cm_bytes = to_bytes![cm]?;
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

        let memo_bytes = to_bytes![transaction.memorandum()]?;
        if self.get_memo_index(&memo_bytes)?.is_some() {
            return Err(StorageError::ExistingMemo(memo_bytes.to_vec()));
        } else {
            ops.push(Op::Insert {
                col: COL_MEMO,
                key: memo_bytes,
                value: (*memo_index as u32).to_le_bytes().to_vec(),
            });
            *memo_index += 1;
        }

        Ok((ops, cms))
    }

    /// Insert a block into storage without canonizing/committing it.
    pub fn insert_only(&self, block: &Block<T>) -> Result<(), StorageError> {
        let block_hash = block.header.get_hash();

        // Check that the block does not already exist.
        if self.block_hash_exists(&block_hash) {
            return Err(StorageError::BlockError(BlockError::BlockExists(
                block_hash.to_string(),
            )));
        }

        let mut database_transaction = DatabaseTransaction::new();

        let mut transaction_serial_numbers = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_commitments = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_memos = Vec::with_capacity(block.transactions.0.len());

        for transaction in &block.transactions.0 {
            transaction_serial_numbers.push(transaction.transaction_id()?);
            transaction_commitments.push(transaction.new_commitments());
            transaction_memos.push(transaction.memorandum());
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

        // Check if the transactions in the block have duplicate memos
        if has_duplicates(transaction_memos) {
            return Err(StorageError::DuplicateMemo);
        }

        for (index, transaction) in block.transactions.0.iter().enumerate() {
            let transaction_location = TransactionLocation {
                index: index as u32,
                block_hash: block.header.get_hash().0,
            };
            database_transaction.push(Op::Insert {
                col: COL_TRANSACTION_LOCATION,
                key: transaction.transaction_id()?.to_vec(),
                value: to_bytes![transaction_location]?.to_vec(),
            });
        }

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_HEADER,
            key: block_hash.0.to_vec(),
            value: to_bytes![block.header]?.to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_TRANSACTIONS,
            key: block.header.get_hash().0.to_vec(),
            value: to_bytes![block.transactions]?.to_vec(),
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
            value: to_bytes![block.transactions]?.to_vec(),
        });

        self.storage.batch(database_transaction)?;

        Ok(())
    }

    /// Commit/canonize a particular block.
    pub fn commit(&self, block: &Block<T>) -> Result<(), StorageError> {
        let block_header_hash = block.header.get_hash();

        // Check if the block is already in the canon chain
        if self.is_canon(&block_header_hash) {
            return Err(StorageError::ExistingCanonBlock(block_header_hash.to_string()));
        }

        let mut database_transaction = DatabaseTransaction::new();

        let mut transaction_serial_numbers = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_commitments = Vec::with_capacity(block.transactions.0.len());
        let mut transaction_memos = Vec::with_capacity(block.transactions.0.len());

        for transaction in &block.transactions.0 {
            transaction_serial_numbers.push(transaction.transaction_id()?);
            transaction_commitments.push(transaction.new_commitments());
            transaction_memos.push(transaction.memorandum());
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

        // Check if the transactions in the block have duplicate memos
        if has_duplicates(transaction_memos) {
            return Err(StorageError::DuplicateMemo);
        }

        let mut sn_index = self.current_sn_index()?;
        let mut cm_index = self.current_cm_index()?;
        let mut memo_index = self.current_memo_index()?;

        // Process the individual transactions

        let mut transaction_cms = vec![];

        for transaction in block.transactions.0.iter() {
            let (tx_ops, cms) = self.commit_transaction(&mut sn_index, &mut cm_index, &mut memo_index, transaction)?;
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
        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_CURR_MEMO_INDEX.as_bytes().to_vec(),
            value: (memo_index as u32).to_le_bytes().to_vec(),
        });

        // Update the best block number

        let height = self.get_current_block_height();

        let is_genesis =
            block.header.previous_block_hash == BlockHeaderHash([0u8; 32]) && height == 0 && self.is_empty();

        let mut new_best_block_number = 0;
        if !is_genesis {
            new_best_block_number = height + 1;
        }

        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_BEST_BLOCK_NUMBER.as_bytes().to_vec(),
            value: new_best_block_number.to_le_bytes().to_vec(),
        });

        // Update the block location

        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: block.header.get_hash().0.to_vec(),
            value: new_best_block_number.to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_BLOCK_LOCATOR,
            key: new_best_block_number.to_le_bytes().to_vec(),
            value: block.header.get_hash().0.to_vec(),
        });

        // Rebuild the new commitment merkle tree
        self.rebuild_merkle_tree(transaction_cms)?;
        let new_digest = self.cm_merkle_tree.read().root();

        database_transaction.push(Op::Insert {
            col: COL_DIGEST,
            key: to_bytes![new_digest]?.to_vec(),
            value: new_best_block_number.to_le_bytes().to_vec(),
        });
        database_transaction.push(Op::Insert {
            col: COL_META,
            key: KEY_CURR_DIGEST.as_bytes().to_vec(),
            value: to_bytes![new_digest]?.to_vec(),
        });

        self.storage.batch(database_transaction)?;

        if !is_genesis {
            self.current_block_height.fetch_add(1, Ordering::SeqCst);
        }

        Ok(())
    }

    /// Insert a block into the storage and commit as part of the longest chain.
    pub fn insert_and_commit(&self, block: &Block<T>) -> Result<(), StorageError> {
        let block_hash = block.header.get_hash();

        // If the block does not exist in the storage
        if !self.block_hash_exists(&block_hash) {
            // Insert it first
            self.insert_only(&block)?;
        }
        // Commit it
        self.commit(block)
    }

    /// Returns true if the block exists in the canon chain.
    pub fn is_canon(&self, block_hash: &BlockHeaderHash) -> bool {
        self.block_hash_exists(block_hash) && self.get_block_number(block_hash).is_ok()
    }
}
