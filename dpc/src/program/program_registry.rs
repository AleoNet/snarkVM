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
use snarkvm_algorithms::{merkle_tree::MerkleTree, prelude::*};
use snarkvm_utilities::{has_duplicates, ToMinimalBits};

use anyhow::{anyhow, Result};
use std::{collections::HashMap, sync::Arc};

/// The on chain program registry to stores all verification keys.
#[derive(Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct ProgramRegistry<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<N::ProgramIDParameters>,
    #[derivative(Debug = "ignore")]
    functions: HashMap<N::FunctionID, <N::ProgramSNARK as SNARK>::VerifyingKey>,
    num_functions: u32,
}

// TODO: Implement program deployment transaction, storage of vks, etc.

// Option 1:
// Deployment transaction:
// - A program tree with a list of function VKS
// - If a function VK already exists - Check that it exists in the current ledger?
// Open question: What is stored on chain? - What does the IR represent?

// Subsequent transaction:
// 1. Transaction is made (deployment of program and its functions).
// 2. Each function is then added to the program registry (or checked if it exists).
// 3. Standard transactions must check that the vk exists in the program registry

impl<N: Network> ProgramRegistry<N> {
    pub fn new(function_vks: Vec<<N::ProgramSNARK as SNARK>::VerifyingKey>) -> Result<Self> {
        // Initialize a new functions tree, and add all functions to the tree.
        let mut registry = Self {
            tree: MerkleTree::<N::ProgramIDParameters>::new::<N::FunctionID>(
                Arc::new(N::program_id_parameters().clone()),
                &[],
            )?,
            functions: Default::default(),
            num_functions: 0,
        };
        registry.add_all(function_vks)?;

        Ok(registry)
    }

    /// Returns `true` if the given function ID exists in the program.
    pub fn contains_function(&self, function_id: &N::FunctionID) -> bool {
        self.functions.get(function_id).is_some()
    }

    /// Adds all given function vks to the tree
    fn add_all(&mut self, function_vks: Vec<<N::ProgramSNARK as SNARK>::VerifyingKey>) -> Result<()> {
        // Ensure the list of given function vks is non-empty.
        if function_vks.is_empty() {
            return Err(anyhow!("The list of given function vks must be non-empty"));
        }

        // Construct a list of function IDs.
        let function_ids: Vec<_> = function_vks
            .iter()
            .map(|vk| N::function_id_crh().hash_bits(&vk.to_minimal_bits()).unwrap().into())
            .collect();

        // Ensure the list of given function IDs is unique.
        if has_duplicates(function_ids.iter()) {
            return Err(anyhow!("The list of given functions contains duplicates"));
        }

        // Ensure the functions do not already exist in the tree.
        if function_ids.iter().any(|id| self.contains_function(id)) {
            return Err(anyhow!("Some given functions already exist in the program"));
        }

        self.tree = self.tree.rebuild(self.num_functions as usize, &function_ids)?;

        let num_functions = function_vks.len();

        self.functions.extend(
            function_ids
                .into_iter()
                .zip(function_vks)
                .enumerate()
                .map(|(_index, (id, vk))| (id, vk)),
        );

        self.num_functions += num_functions as u32;

        Ok(())
    }
}
