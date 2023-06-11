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

use crate::{
    process::{FinalizeTypes, RegistersLoad, RegistersStore, StackMatches, StackProgram},
    program::Operand,
};
use console::{
    network::prelude::*,
    program::{Literal, Plaintext, Register, Value},
};

use indexmap::IndexMap;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FinalizeGlobalState {
    /// The block height.
    block_height: u32,
}

impl FinalizeGlobalState {
    /// Initializes a new global state.
    #[inline]
    pub const fn new(block_height: u32) -> Self {
        Self { block_height }
    }

    /// Returns the block height.
    #[inline]
    pub const fn block_height(&self) -> u32 {
        self.block_height
    }
}

#[derive(Clone)]
pub struct FinalizeRegisters<N: Network> {
    /// The global state for the finalize scope.
    state: FinalizeGlobalState,
    /// The mapping of all registers to their defined types.
    finalize_types: FinalizeTypes<N>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, Plaintext<N>>,
}

impl<N: Network> FinalizeRegisters<N> {
    /// Initializes a new set of registers, given the finalize types.
    #[inline]
    pub fn new(state: FinalizeGlobalState, finalize_types: FinalizeTypes<N>) -> Self {
        Self { state, finalize_types, registers: IndexMap::new() }
    }

    /// Returns the global state for the finalize scope.
    #[inline]
    pub const fn state(&self) -> &FinalizeGlobalState {
        &self.state
    }
}
