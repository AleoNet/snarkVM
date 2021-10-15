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

use crate::prelude::*;
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A serial numbers tree contains all serial numbers on the ledger.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct SerialNumbers<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::SerialNumbersTreeParameters>>,
    serial_numbers: HashMap<N::SerialNumber, u64>,
    current_index: u64,
}

impl<N: Network> SerialNumbersTreeScheme<N> for SerialNumbers<N> {
    /// Initializes an empty serial numbers tree.
    fn new() -> Result<Self> {
        Ok(Self {
            tree: Arc::new(MerkleTree::<N::SerialNumbersTreeParameters>::new::<N::SerialNumber>(
                Arc::new(N::serial_numbers_tree_parameters().clone()),
                &vec![],
            )?),
            serial_numbers: Default::default(),
            current_index: 0,
        })
    }

    /// TODO (howardwu): Add safety checks for u64 (max 2^42).
    /// Adds the given serial number to the tree, returning its index in the tree.
    fn add(&mut self, serial_number: &N::SerialNumber) -> Result<u64> {
        // Ensure the serial number does not already exist in the tree.
        if self.contains_serial_number(serial_number) {
            return Err(
                MerkleError::Message(format!("{} already exists in the serial numbers tree", serial_number)).into(),
            );
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &[serial_number])?);

        self.serial_numbers.insert(*serial_number, self.current_index);

        self.current_index += 1;
        Ok(self.current_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u64 (max 2^42).
    /// Adds all given serial numbers to the tree, returning the start and ending index in the tree.
    fn add_all(&mut self, serial_numbers: &[N::SerialNumber]) -> Result<(u64, u64)> {
        // Ensure the list of given serial_numbers is non-empty.
        if serial_numbers.is_empty() {
            return Err(anyhow!("The list of given serial numbers must be non-empty"));
        }

        // Ensure the list of given serial_numbers is unique.
        if has_duplicates(serial_numbers.iter()) {
            return Err(anyhow!("The list of given serial numbers contains duplicates"));
        }

        // Ensure the serial_numbers do not already exist in the tree.
        let duplicate_serial_numbers: Vec<_> = serial_numbers
            .iter()
            .filter(|s| self.contains_serial_number(s))
            .collect();
        if !duplicate_serial_numbers.is_empty() {
            return Err(anyhow!("The list of given serial numbers contains double spends"));
        }

        self.tree = Arc::new(self.tree.rebuild(self.current_index as usize, &serial_numbers)?);

        let start_index = self.current_index;
        let num_serial_numbers = serial_numbers.len();

        self.serial_numbers.extend(
            serial_numbers
                .into_iter()
                .enumerate()
                .map(|(index, serial_number)| (*serial_number, start_index + index as u64)),
        );

        self.current_index += num_serial_numbers as u64;
        let end_index = self.current_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given serial number exists.
    fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.serial_numbers.contains_key(serial_number)
    }

    /// Returns the index for the given serial number, if it exists.
    fn get_serial_number_index(&self, serial_number: &N::SerialNumber) -> Option<&u64> {
        self.serial_numbers.get(serial_number)
    }

    /// Returns the serial numbers root.
    fn root(&self) -> N::SerialNumbersRoot {
        *self.tree.root()
    }

    /// Returns the Merkle path for a given serial number.
    fn to_serial_number_inclusion_proof(
        &self,
        serial_number: &N::SerialNumber,
    ) -> Result<MerklePath<N::SerialNumbersTreeParameters>> {
        match self.get_serial_number_index(serial_number) {
            Some(index) => Ok(self.tree.generate_proof(*index as usize, serial_number)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", serial_number)).into()),
        }
    }
}

impl<N: Network> Default for SerialNumbers<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
