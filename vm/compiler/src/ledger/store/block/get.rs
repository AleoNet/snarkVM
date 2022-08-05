// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use super::*;

impl<N: Network, B: BlockStorage<N>> BlockStore<N, B> {
    /// Returns the block height for the given block hash.
    pub fn get_height(&self, hash: N::BlockHash) -> Result<u32> {
        match self.headers.get(&hash)? {
            Some(header) => Ok(header.metadata().height()),
            None => bail!("Missing block header for block hash {hash}"),
        }
    }

    /// Returns the block hash for the given block height.
    pub fn get_hash(&self, height: u32) -> Result<N::BlockHash> {
        match self.hashes.get(&height)? {
            Some(hash) => Ok(*hash),
            None => bail!("Missing block hash for block {height}"),
        }
    }

    /// Returns the previous block hash for the given block height.
    pub fn get_previous_hash(&self, height: u32) -> Result<N::BlockHash> {
        match height {
            0 => Ok(N::BlockHash::default()),
            height => self.get_hash(height.saturating_sub(1)),
        }
    }

    /// Returns the block header for the given block height.
    pub fn get_header(&self, height: u32) -> Result<Cow<'_, Header<N>>> {
        match self.headers.get(&*self.get_hash(height)?)? {
            Some(header) => Ok(header),
            None => bail!("Missing block header for block {height}"),
        }
    }

    /// Returns the block signature for the given block height.
    pub fn get_signature(&self, height: u32) -> Result<Cow<'_, Signature<N>>> {
        match self.signatures.get(&*self.get_hash(height)?)? {
            Some(signature) => Ok(signature),
            None => bail!("Missing signature for block {height}"),
        }
    }
}
