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

mod load;
mod store;

use crate::{FinalizeTypes, Operand, Stack};
use console::{
    network::prelude::*,
    program::{Entry, Literal, Plaintext, Register, Value},
};

use indexmap::IndexMap;

#[derive(Clone)]
pub struct FinalizeRegisters<N: Network> {
    /// The mapping of all registers to their defined types.
    finalize_types: FinalizeTypes<N>,
    /// The mapping of assigned registers to their values.
    registers: IndexMap<u64, Value<N>>,
}

impl<N: Network> FinalizeRegisters<N> {
    /// Initializes a new set of registers, given the finalize types.
    #[inline]
    pub fn new(finalize_types: FinalizeTypes<N>) -> Self {
        Self { finalize_types, registers: IndexMap::new() }
    }
}
