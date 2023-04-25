// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#[derive(Clone)]
pub enum Query<N: Network, B: BlockStorage<N>> {
    /// The block store from the VM.
    VM(BlockStore<N, B>),
    /// The base URL of the node.
    REST(String),
}

impl<N: Network, B: BlockStorage<N>> From<BlockStore<N, B>> for Query<N, B> {
    fn from(block_store: BlockStore<N, B>) -> Self {
        Self::VM(block_store)
    }
}

impl<N: Network, B: BlockStorage<N>> From<&BlockStore<N, B>> for Query<N, B> {
    fn from(block_store: &BlockStore<N, B>) -> Self {
        Self::VM(block_store.clone())
    }
}

impl<N: Network, B: BlockStorage<N>> From<String> for Query<N, B> {
    fn from(url: String) -> Self {
        Self::REST(url)
    }
}

impl<N: Network, B: BlockStorage<N>> From<&String> for Query<N, B> {
    fn from(url: &String) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> From<&str> for Query<N, B> {
    fn from(url: &str) -> Self {
        Self::REST(url.to_string())
    }
}

impl<N: Network, B: BlockStorage<N>> Query<N, B> {
    /// Returns the program for the given program ID.
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<Program<N>> {
        match self {
            Self::VM(block_store) => {
                block_store.get_program(program_id)?.ok_or_else(|| anyhow!("Program {program_id} not found in storage"))
            }
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/program/{program_id}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("Synchronous API calls not supported from WASM"),
        }
    }

    /// Returns the current state root.
    pub fn current_state_root(&self) -> Result<N::StateRoot> {
        match self {
            Self::VM(block_store) => Ok(block_store.current_state_root()),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/latest/stateRoot"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("Synchronous external API calls not supported from WASM"),
        }
    }

    /// Returns a state path for the given `commitment`.
    pub fn get_state_path_for_commitment(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        match self {
            Self::VM(block_store) => block_store.get_state_path_for_commitment(commitment),
            #[cfg(not(feature = "wasm"))]
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/statePath/{commitment}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
            #[cfg(feature = "wasm")]
            _ => bail!("Synchronous external API calls not supported from WASM"),
        }
    }

    /// Performs a GET request to the given URL.
    #[cfg(not(feature = "wasm"))]
    fn get_request(url: &str) -> Result<ureq::Response> {
        let response = ureq::get(url).call()?;
        if response.status() == 200 { Ok(response) } else { bail!("Failed to fetch from {}", url) }
    }
}
