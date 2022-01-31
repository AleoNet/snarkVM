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
#[derivative(Debug(bound = "N: Network"), Clone(bound = "N: Network"))]
pub struct ProgramRegistry<N: Network> {
    #[derivative(Debug = "ignore")]
    tree: Arc<MerkleTree<N::ProgramIDParameters>>, // TODO (raychu86): Possibly introduce a new parameter here.
    #[derivative(Debug = "ignore")]
    programs: HashMap<N::ProgramID, ProgramFunctions<N>>, // TODO (raychu86): Replace vk with circuit IR.
    num_programs: u32,
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
    pub fn new() -> Result<Self> {
        // Initialize a new functions tree, and add all functions to the tree.
        let mut registry = Self {
            tree: Arc::new(MerkleTree::<N::ProgramIDParameters>::new::<N::FunctionID>(
                Arc::new(N::program_id_parameters().clone()),
                &[],
            )?),
            programs: Default::default(),
            num_programs: 0,
        };

        // Add the noop program.
        registry.add((
            *N::noop_program_id(),
            ProgramFunctions([(*N::noop_function_id(), N::noop_circuit_verifying_key().clone())].into()),
        ))?;

        Ok(registry)
    }

    /// Returns `true` if the given program ID exists in the program registry.
    pub fn contains_program(&self, program_id: &N::ProgramID) -> bool {
        self.programs.get(program_id).is_some()
    }

    /// Add a program vks to the tree
    pub(crate) fn add(&mut self, program: (N::ProgramID, ProgramFunctions<N>)) -> Result<()> {
        // Ensure the list of given function vks is non-empty.
        if program.1.0.is_empty() {
            return Err(anyhow!("The list of given function vks must be non-empty"));
        }

        // TODO (raychu86): Enforce that the program vks match the program id.

        // Construct a list of function IDs.
        let function_ids: Vec<N::FunctionID> = program
            .1
            .0
            .iter()
            .map(|(id, vk)| {
                let function_id = N::function_id_crh().hash_bits(&vk.to_minimal_bits()).unwrap().into();

                assert_eq!(&function_id, id);

                function_id
            })
            .collect();

        // Ensure the list of given function IDs is unique.
        if has_duplicates(function_ids.iter()) {
            return Err(anyhow!("The list of given functions contains duplicates"));
        }

        // Ensure the program doe not already exist in the tree.
        if self.contains_program(&program.0) {
            return Err(anyhow!("The program already exists in the registry"));
        }

        self.tree = Arc::new(self.tree.rebuild(self.num_programs as usize, &[program.0])?);
        self.programs.insert(program.0, program.1);
        self.num_programs += 1;

        Ok(())
    }

    /// Adds all given programs to the tree.
    pub(crate) fn add_all(&mut self, programs: Vec<(N::ProgramID, ProgramFunctions<N>)>) -> Result<()> {
        // TODO (raychu86): Optimize this operation.
        for program in programs {
            self.add(program)?;
        }

        Ok(())
    }
}
