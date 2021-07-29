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

use crate::Parameters;
use snarkvm_algorithms::{
    merkle_tree::{MerklePath, MerkleTree},
    prelude::*,
};
use std::sync::Arc;

// TODO (raychu86): May just want to use the merkle tree struct directly.
//  Added as a struct in case additional functionality is needed for the program selector tree.

/// The program selector tree used to construct the record birth/death program root.
pub struct ProgramSelectorTree<C: Parameters>(MerkleTree<C::ProgramSelectorTreeParameters>);

impl<C: Parameters> ProgramSelectorTree<C> {
    pub fn new(program_ids: Vec<Vec<u8>>) -> Result<Self, MerkleError> {
        let program_selector_tree = MerkleTree::<C::ProgramSelectorTreeParameters>::new(
            Arc::new(C::program_selector_tree_parameters().clone()),
            &program_ids,
        )?;

        Ok(Self(program_selector_tree))
    }

    pub fn generate_program_path(
        &self,
        index: usize,
        program_id: &Vec<u8>,
    ) -> Result<MerklePath<C::ProgramSelectorTreeParameters>, MerkleError> {
        self.0.generate_proof(index, &program_id)
    }
}
