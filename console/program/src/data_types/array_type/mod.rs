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

mod bytes;
mod parse;
mod serialize;

use snarkvm_console_network::prelude::*;

use crate::{ElementType, PlaintextType};
use core::fmt::{self, Debug, Display};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ArrayType<N: Network> {
    /// The element type.
    element_type: ElementType<N>,
    /// The dimensions of the array.
    dimensions: Vec<u64>,
}

impl<N: Network> ArrayType<N> {
    /// Constructs a new array type.
    pub fn new(element_type: ElementType<N>, dimensions: Vec<u64>) -> Result<Self> {
        ensure!(!dimensions.is_empty(), "Cannot have an empty array");
        ensure!(dimensions.len() < N::MAX_DATA_DEPTH);
        for dimension in &dimensions {
            ensure!(dimension != 0, "Cannot have an array dimension of zero")
        }
        // TODO (d0cd): Should each dimension of the array be restricted to N::MAX_DATA_ENTRIES?
        //  Initial thoughts are no since it feels restrictive, but we may have to do this due to the merklization.

        Ok(Self { element_type, dimensions })
    }

    /// Returns the element type.
    pub fn element_type(&self) -> &PlaintextType<N> {
        &self.element_type
    }

    /// Returns the dimensions of the array.
    pub fn dimensions(&self) -> &[u64] {
        &self.dimensions
    }

    /// Returns the length of the array.
    pub fn length(&self) -> u64 {
        // Note the unwrap is safe since `ArrayType` must have at least one element in `self.dimensions`.
        *self.dimensions.last().unwrap()
    }
}
