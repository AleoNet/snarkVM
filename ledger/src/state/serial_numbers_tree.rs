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

use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use snarkvm_dpc::prelude::*;
use snarkvm_utilities::has_duplicates;

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// A serial numbers tree contains all serial numbers on the ledger.
#[derive(Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct SerialNumbersTree<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<N::SerialNumbersTreeParameters>,
    serial_numbers: HashMap<N::SerialNumber, u32>,
    current_index: u32,
}

impl<N: Network> SerialNumbersTree<N> {
    /// Initializes an empty serial numbers tree.
    pub fn new() -> Result<Self> {
        Ok(Self {
            tree: MerkleTree::<N::SerialNumbersTreeParameters>::new::<N::SerialNumber>(
                Arc::new(N::serial_numbers_tree_parameters().clone()),
                &vec![],
            )?,
            serial_numbers: Default::default(),
            current_index: 0,
        })
    }

    /// TODO (howardwu): Add safety checks for u32 (max 2^32).
    /// Adds the given serial number to the tree, returning its index in the tree.
    pub fn add(&mut self, serial_number: &N::SerialNumber) -> Result<u32> {
        // Ensure the serial number does not already exist in the tree.
        if self.contains_serial_number(serial_number) {
            return Err(
                MerkleError::Message(format!("{} already exists in the serial numbers tree", serial_number)).into(),
            );
        }

        self.tree = self.tree.rebuild(self.current_index as usize, &[serial_number])?;

        self.serial_numbers.insert(*serial_number, self.current_index);

        self.current_index += 1;
        Ok(self.current_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u32 (max 2^32).
    /// Adds all given serial numbers to the tree, returning the start and ending index in the tree.
    pub fn add_all(&mut self, serial_numbers: Vec<N::SerialNumber>) -> Result<(u32, u32)> {
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

        self.tree = self.tree.rebuild(self.current_index as usize, &serial_numbers)?;

        let start_index = self.current_index;
        let num_serial_numbers = serial_numbers.len();

        self.serial_numbers.extend(
            serial_numbers
                .into_iter()
                .enumerate()
                .map(|(index, serial_number)| (serial_number, start_index + index as u32)),
        );

        self.current_index += num_serial_numbers as u32;
        let end_index = self.current_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &N::SerialNumber) -> bool {
        self.serial_numbers.contains_key(serial_number)
    }

    /// Returns the index for the given serial number, if it exists.
    pub fn get_serial_number_index(&self, serial_number: &N::SerialNumber) -> Option<&u32> {
        self.serial_numbers.get(serial_number)
    }

    /// Returns the Merkle path for a given serial number.
    pub fn to_inclusion_proof(
        &self,
        serial_number: &N::SerialNumber,
    ) -> Result<MerklePath<N::SerialNumbersTreeParameters>> {
        match self.get_serial_number_index(serial_number) {
            Some(index) => Ok(self.tree.generate_proof(*index as usize, serial_number)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", serial_number)).into()),
        }
    }

    /// Returns the serial numbers root.
    pub fn to_serial_numbers_root(&self) -> &N::SerialNumbersRoot {
        self.tree.root()
    }
}

impl<N: Network> Default for SerialNumbersTree<N> {
    fn default() -> Self {
        Self::new().unwrap()
    }
}
