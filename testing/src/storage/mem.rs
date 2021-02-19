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

use snarkvm_errors::objects::StorageError;
use snarkvm_models::objects::{Storage, StorageBatchOp, StorageOp};
use snarkvm_storage::NUM_COLS;

use parking_lot::RwLock;

use std::{collections::HashMap, path::Path};

pub struct MemDb {
    pub cols: RwLock<Vec<HashMap<Box<[u8]>, Box<[u8]>>>>,
}

impl Storage for MemDb {
    fn in_memory(&self) -> bool {
        true
    }

    fn open(path: Option<&Path>, secondary_path: Option<&Path>) -> Result<Self, StorageError> {
        assert!(
            path.is_none() && secondary_path.is_none(),
            "MemDb has no associated filesystem paths!"
        );

        Ok(Self {
            cols: RwLock::new(vec![Default::default(); NUM_COLS as usize]),
        })
    }

    fn get(&self, col: u32, key: &[u8]) -> Result<Option<Vec<u8>>, StorageError> {
        Ok(self.cols.read()[col as usize].get(key).map(|v| v.to_vec()))
    }

    fn get_col(&self, col: u32) -> Result<Vec<(Box<[u8]>, Box<[u8]>)>, StorageError> {
        Ok(self.cols.read()[col as usize].clone().into_iter().collect())
    }

    fn get_keys(&self, col: u32) -> Result<Vec<Box<[u8]>>, StorageError> {
        Ok(self.cols.read()[col as usize].keys().cloned().collect())
    }

    fn put<K: AsRef<[u8]>, V: AsRef<[u8]>>(&self, col: u32, key: K, value: V) -> Result<(), StorageError> {
        self.cols.write()[col as usize].insert(key.as_ref().into(), value.as_ref().into());
        Ok(())
    }

    fn batch(&self, transaction: StorageBatchOp) -> Result<(), StorageError> {
        if transaction.0.is_empty() {
            return Ok(());
        }

        let mut cols = self.cols.write();
        for operation in transaction.0 {
            match operation {
                StorageOp::Insert { col, key, value } => {
                    cols[col as usize].insert(key.into(), value.into());
                }
                StorageOp::Delete { col, key } => {
                    cols[col as usize].remove(&Box::from(key));
                }
            }
        }

        Ok(())
    }

    fn exists(&self, col: u32, key: &[u8]) -> bool {
        self.cols.read()[col as usize].contains_key(key)
    }

    fn try_catch_up_with_primary(&self) -> Result<(), StorageError> {
        Ok(()) // there's no secondary instance
    }

    fn destroy(&self) -> Result<(), StorageError> {
        Ok(()) // nothing to do here: the Drop impl takes care of the associated in-memory objects
    }
}
