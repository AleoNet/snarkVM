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

use crate::errors::StorageError;

use std::{fmt::Debug, path::Path};

pub trait Storage
where
    Self: Sized,
{
    /// A `bool` indicating whether the storage is in-memory only.
    const IN_MEMORY: bool;

    /// Opens the storage object, optionally using the given paths; it gets created if it doesn't exist.
    fn open(path: Option<&Path>, secondary_path: Option<&Path>) -> Result<Self, StorageError>;

    /// Returns the value with the given key and belonging to the given column.
    fn get(&self, col: u32, key: &[u8]) -> Result<Option<Vec<u8>>, StorageError>;

    /// Returns all the keys and values belonging to the given column.
    #[allow(clippy::type_complexity)]
    fn get_col(&self, col: u32) -> Result<Vec<(Box<[u8]>, Box<[u8]>)>, StorageError>;

    /// Returns all the keys belonging to the given column.
    fn get_keys(&self, col: u32) -> Result<Vec<Box<[u8]>>, StorageError>;

    /// Stores the given key and value in the specified column.
    fn put<K: AsRef<[u8]>, V: AsRef<[u8]>>(&self, col: u32, key: K, value: V) -> Result<(), StorageError>;

    /// Executes the given `DatabaseTransaction` as a batch operation.
    fn batch(&self, batch: DatabaseTransaction) -> Result<(), StorageError>;

    /// Returns `true` if the given key exists in the speficied column.
    fn exists(&self, col: u32, key: &[u8]) -> bool;

    // Attempts to catch up the read-only secondary instance with the primary one.
    fn try_catch_up_with_primary(&self) -> Result<(), StorageError>;
}

/// Database operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Insert { col: u32, key: Vec<u8>, value: Vec<u8> },
    Delete { col: u32, key: Vec<u8> },
}

/// Batched transaction of database operations.
#[derive(Default, Clone, PartialEq)]
pub struct DatabaseTransaction(pub Vec<Op>);

impl DatabaseTransaction {
    /// Create new transaction.
    pub fn new() -> Self {
        Self(vec![])
    }

    /// Add an operation.
    pub fn push(&mut self, op: Op) {
        self.0.push(op)
    }

    /// Add a vector of operations.
    pub fn push_vec(&mut self, ops: Vec<Op>) {
        self.0.extend(ops)
    }
}
