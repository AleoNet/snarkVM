// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod load;
mod store;

use crate::process::{FinalizeTypes, RegistersLoad, RegistersStore, StackMatches, StackProgram};
use console::{
    network::prelude::*,
    program::{Identifier, Literal, Plaintext, Register, Value},
    types::U32,
};
use snarkvm_synthesizer_program::Operand;

use indexmap::IndexMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FinalizeGlobalState {
    /// The block height.
    block_height: u32,
    /// The block-specific random seed.
    random_seed: [u8; 32],
}

impl FinalizeGlobalState {
    /// Initializes a new global state from the given inputs.
    #[inline]
    pub fn new<N: Network>(
        block_round: u64,
        block_height: u32,
        block_cumulative_weight: u128,
        block_cumulative_proof_target: u128,
        previous_block_hash: N::BlockHash,
    ) -> Result<Self> {
        // Initialize the preimage.
        let mut preimage = Vec::with_capacity(605);
        preimage.extend_from_slice(&block_round.to_bits_le());
        preimage.extend_from_slice(&block_height.to_bits_le());
        preimage.extend_from_slice(&block_cumulative_weight.to_bits_le());
        preimage.extend_from_slice(&block_cumulative_proof_target.to_bits_le());
        preimage.extend_from_slice(&(*previous_block_hash).to_bits_le());

        // Hash the preimage to get the random seed.
        let seed = N::hash_bhp768(&preimage)?.to_bytes_le()?;
        // Ensure the seed is 32-bytes.
        ensure!(seed.len() == 32, "Invalid seed length for finalize global state.");

        // Convert the seed into a 32-byte array.
        let mut random_seed = [0u8; 32];
        random_seed.copy_from_slice(&seed[..32]);

        Ok(Self { block_height, random_seed })
    }

    /// Initializes a new global state.
    #[inline]
    pub const fn from(block_height: u32, random_seed: [u8; 32]) -> Self {
        Self { block_height, random_seed }
    }

    /// Returns the block height.
    #[inline]
    pub const fn block_height(&self) -> u32 {
        self.block_height
    }

    /// Returns the random seed.
    #[inline]
    pub const fn random_seed(&self) -> &[u8; 32] {
        &self.random_seed
    }
}

#[derive(Clone)]
pub struct FinalizeRegisters<N: Network> {
    /// The global state for the finalize scope.
    state: FinalizeGlobalState,
    /// The transition ID for the finalize scope.
    transition_id: N::TransitionID,
    /// The function name for the finalize scope.
    function_name: Identifier<N>,
    /// The mapping of all registers to their defined types.
    finalize_types: FinalizeTypes<N>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, Plaintext<N>>,
}

impl<N: Network> FinalizeRegisters<N> {
    /// Initializes a new set of registers, given the finalize types.
    #[inline]
    pub fn new(
        state: FinalizeGlobalState,
        transition_id: N::TransitionID,
        function_name: Identifier<N>,
        finalize_types: FinalizeTypes<N>,
    ) -> Self {
        Self { state, transition_id, finalize_types, function_name, registers: IndexMap::new() }
    }

    /// Returns the global state for the finalize scope.
    #[inline]
    pub const fn state(&self) -> &FinalizeGlobalState {
        &self.state
    }

    /// Returns the transition ID for the finalize scope.
    #[inline]
    pub const fn transition_id(&self) -> &N::TransitionID {
        &self.transition_id
    }

    /// Returns the function name for the finalize scope.
    #[inline]
    pub const fn function_name(&self) -> &Identifier<N> {
        &self.function_name
    }
}
