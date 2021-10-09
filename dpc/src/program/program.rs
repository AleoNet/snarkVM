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

/// A program defines all possible state transitions for a record.
#[derive(Derivative)]
#[derivative(Debug(bound = "N: Network"))]
pub struct Program<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: MerkleTree<N::ProgramFunctionsTreeParameters>,
    #[derivative(Debug = "ignore")]
    functions: HashMap<N::FunctionID, (u8, Arc<dyn Function<N>>)>,
    last_function_index: u8,
}

impl<N: Network> ProgramScheme<N> for Program<N> {
    /// Initializes an instance of the program with the given functions.
    fn new(functions: Vec<Arc<dyn Function<N>>>) -> Result<Self> {
        // Initialize a new functions tree, and add all functions to the tree.
        let mut program = Self {
            tree: MerkleTree::<N::ProgramFunctionsTreeParameters>::new::<N::FunctionID>(
                Arc::new(N::program_functions_tree_parameters().clone()),
                &vec![],
            )?,
            functions: Default::default(),
            last_function_index: 0,
        };
        program.add_all(functions)?;

        Ok(program)
    }

    /// Initializes an instance of the noop program.
    fn new_noop() -> Result<Self> {
        // Initialize a new functions tree, and add all functions to the tree.
        let mut program = Self {
            tree: MerkleTree::<N::ProgramFunctionsTreeParameters>::new::<N::FunctionID>(
                Arc::new(N::program_functions_tree_parameters().clone()),
                &vec![],
            )?,
            functions: Default::default(),
            last_function_index: 0,
        };
        program.add(Arc::new(Noop::<N>::new()))?;

        Ok(program)
    }

    /// Returns the program ID.
    fn program_id(&self) -> N::ProgramID {
        *self.tree.root()
    }

    /// Returns `true` if the given function ID exists in the program.
    fn contains_function(&self, function_id: &N::FunctionID) -> bool {
        self.functions.get(function_id).is_some()
    }

    /// Returns the function given the function ID, if it exists.
    fn to_function(&self, function_id: &N::FunctionID) -> Result<Arc<dyn Function<N>>> {
        match self.functions.get(function_id) {
            Some((_, function)) => {
                debug_assert_eq!(function.function_id(), *function_id);
                Ok(function.clone())
            }
            _ => Err(MerkleError::MissingLeaf(format!("{}", function_id)).into()),
        }
    }

    /// Returns the program path (the Merkle path for a given function ID).
    fn to_program_path(&self, function_id: &N::FunctionID) -> Result<MerklePath<N::ProgramFunctionsTreeParameters>> {
        match self.get_function_index(function_id) {
            Some(index) => Ok(self.tree.generate_proof(index as usize, function_id)?),
            _ => Err(MerkleError::MissingLeaf(format!("{}", function_id)).into()),
        }
    }
}

impl<N: Network> Program<N> {
    /// TODO (howardwu): Add safety checks for u8 (max 255 functions).
    /// Adds the given function to the tree, returning its function index in the tree.
    fn add(&mut self, function: Arc<dyn Function<N>>) -> Result<u8> {
        // Ensure the function does not already exist in the tree.
        if self.contains_function(&function.function_id()) {
            return Err(MerkleError::Message(format!("Duplicate function {}", function.function_id())).into());
        }

        self.tree = self
            .tree
            .rebuild(self.last_function_index as usize, &[function.function_id()])?;

        self.functions
            .insert(function.function_id().clone(), (self.last_function_index, function));

        self.last_function_index += 1;
        Ok(self.last_function_index - 1)
    }

    /// TODO (howardwu): Add safety checks for u8 (max 255 functions).
    /// Adds all given functions to the tree, returning the start and ending function index in the tree.
    fn add_all(&mut self, functions: Vec<Arc<dyn Function<N>>>) -> Result<(u8, u8)> {
        // Ensure the list of given functions is non-empty.
        if functions.is_empty() {
            return Err(anyhow!("The list of given functions must be non-empty"));
        }

        // Construct a list of function IDs.
        let function_ids: Vec<_> = functions.iter().map(|c| c.function_id()).collect();

        // Ensure the list of given function IDs is unique.
        if has_duplicates(function_ids.iter()) {
            return Err(anyhow!("The list of given functions contains duplicates"));
        }

        // Ensure the functions do not already exist in the tree.
        let duplicate_functions: Vec<_> = function_ids.iter().filter(|id| self.contains_function(id)).collect();
        if !duplicate_functions.is_empty() {
            return Err(anyhow!("Some given functions already exist in the program"));
        }

        self.tree = self.tree.rebuild(self.last_function_index as usize, &function_ids)?;

        let start_index = self.last_function_index;
        let num_functions = functions.len();

        self.functions.extend(
            functions
                .into_iter()
                .enumerate()
                .map(|(index, function)| (function.function_id().clone(), (start_index + index as u8, function))),
        );

        self.last_function_index += num_functions as u8;
        let end_index = self.last_function_index - 1;

        Ok((start_index, end_index))
    }

    /// Returns the function given the function index, if it exists.
    fn find_function_by_index(&self, function_index: u8) -> Option<&Arc<dyn Function<N>>> {
        self.functions
            .iter()
            .find_map(|(_, (index, function))| match *index == function_index {
                true => Some(function),
                false => None,
            })
    }

    /// Returns the function index given the function ID, if it exists.
    fn get_function_index(&self, function_id: &N::FunctionID) -> Option<u8> {
        self.functions.get(function_id).and_then(|(index, _)| Some(*index))
    }
}
