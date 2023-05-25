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

#[derive(Clone)]
pub struct FinalizeRegisters<N: Network> {
    /// The mapping of all registers to their defined types.
    finalize_types: FinalizeTypes<N>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, Plaintext<N>>,
}

impl<N: Network> FinalizeRegisters<N> {
    /// Initializes a new set of registers, given the finalize types.
    #[inline]
    pub fn new(finalize_types: FinalizeTypes<N>) -> Self {
        Self { finalize_types, registers: IndexMap::new() }
    }
}
