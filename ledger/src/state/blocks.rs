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

use crate::Environment;
use snarkvm_dpc::prelude::*;

use anyhow::{anyhow, Result};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Blocks<E: Environment> {
    blocks: HashMap<u32, Block<E::Network>>,
}

impl<E: Environment> Blocks<E> {
    /// Initializes a new instance of `Blocks`.
    pub fn new() -> Self {
        Self {
            blocks: Default::default(),
        }
    }

    pub fn add(&mut self, block: Block<E::Network>) -> Result<()> {
        // Ensure the block does not already exist in the list.
        if self.blocks.contains_key(&block.height()) {
            return Err(anyhow!("The given block already exists in the list"));
        }

        // Ensure the given block is valid.
        if !block.is_valid() {
            return Err(anyhow!("The given block is invalid"));
        }

        self.blocks.insert(block.height(), block);

        Ok(())
    }
}
