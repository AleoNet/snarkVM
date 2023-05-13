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

use crate::{BlockStorage, BlockStore, Program};
use console::{
    network::prelude::*,
    program::{ProgramID, StatePath},
    types::Field,
};

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
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/program/{program_id}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Returns the program for the given program ID.
    pub async fn get_program_async(&self, program_id: &ProgramID<N>) -> Result<Program<N>> {
        match self {
            Self::VM(block_store) => {
                block_store.get_program(program_id)?.ok_or_else(|| anyhow!("Program {program_id} not found in storage"))
            }
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request_async(&format!("{url}/testnet3/program/{program_id}")).await?.json().await?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Returns the current state root.
    pub fn current_state_root(&self) -> Result<N::StateRoot> {
        match self {
            Self::VM(block_store) => Ok(block_store.current_state_root()),
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/latest/stateRoot"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Returns the current state root.
    pub async fn current_state_root_async(&self) -> Result<N::StateRoot> {
        match self {
            Self::VM(block_store) => Ok(block_store.current_state_root()),
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request_async(&format!("{url}/testnet3/latest/stateRoot")).await?.json().await?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Returns a state path for the given `commitment`.
    pub fn get_state_path_for_commitment(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        match self {
            Self::VM(block_store) => block_store.get_state_path_for_commitment(commitment),
            Self::REST(url) => match N::ID {
                3 => Ok(Self::get_request(&format!("{url}/testnet3/statePath/{commitment}"))?.into_json()?),
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Returns a state path for the given `commitment`.
    pub async fn get_state_path_for_commitment_async(&self, commitment: &Field<N>) -> Result<StatePath<N>> {
        match self {
            Self::VM(block_store) => block_store.get_state_path_for_commitment(commitment),
            Self::REST(url) => match N::ID {
                3 => {
                    Ok(Self::get_request_async(&format!("{url}/testnet3/statePath/{commitment}")).await?.json().await?)
                }
                _ => bail!("Unsupported network ID in inclusion query"),
            },
        }
    }

    /// Performs a GET request to the given URL.
    fn get_request(url: &str) -> Result<ureq::Response> {
        let response = ureq::get(url).call()?;
        if response.status() == 200 { Ok(response) } else { bail!("Failed to fetch from {url}") }
    }

    /// Performs a GET request to the given URL.
    async fn get_request_async(url: &str) -> Result<reqwest::Response> {
        let response = reqwest::get(url).await?;
        if response.status() == 200 { Ok(response) } else { bail!("Failed to fetch from {url}") }
    }
}
