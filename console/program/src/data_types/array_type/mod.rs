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

use crate::ElementType;
use snarkvm_console_network::prelude::*;

use core::fmt::{Debug, Display};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ArrayType<N: Network> {
    /// The element type.
    element_type: ElementType<N>,
    /// The dimensions of the array.
    dimensions: Vec<u32>,
}

impl<N: Network> ArrayType<N> {
    /// Constructs a new array type.
    // Note: `dimensions` needs to be explicitly specified since Rust does not yet support generic parameters in const operations.
    pub fn new(element_type: ElementType<N>, dimensions: Vec<u32>) -> Result<Self> {
        ensure!(dimensions.len() != 0, "The array must have at least one dimension");
        ensure!(
            dimensions.len() <= N::MAX_DATA_DEPTH,
            "A multi-dimensional array cannot exceed the maximum data depth of '{}'",
            N::MAX_DATA_DEPTH
        );
        for dimension in &dimensions {
            ensure!(*dimension != 0, "Cannot have a zero-valued dimension")
        }
        // TODO (d0cd): Should each dimension of the array be restricted to N::MAX_DATA_ENTRIES?
        //  Initial thoughts are no since it feels restrictive, but we may have to do this due to the merklization.

        Ok(Self { element_type, dimensions })
    }

    /// Returns the element type.
    pub fn element_type(&self) -> &ElementType<N> {
        &self.element_type
    }

    /// Returns the dimensions of the array.
    pub fn dimensions(&self) -> &[u32] {
        &self.dimensions
    }

    /// Returns the length of the array.
    pub fn length(&self) -> u32 {
        // Note the unwrap is safe since `self.dimensions` must have at least one element.
        *self.dimensions.last().unwrap()
    }
}
