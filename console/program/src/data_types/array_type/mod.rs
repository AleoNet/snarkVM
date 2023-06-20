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

// Note: `MAX_DIMENSIONS` needs to be explicitly specified since Rust does not yet support generic parameters in const operations.
pub type ArrayType<N> = GenericArrayType<N, 32>;

// TODO (d0cd): Attempt to enforce more type safety in the ArrayType
//  - Consider using `NonzeroU8` for `num_dimensions`
//  - Find a way to enforce size the static size of `dimensions`.
// TODO (d0cd): This implementation of `ArrayType` results in a stack entry of ~136 bytes.
//  - Instead if arrays were non-copy, we could store a reference to the `dimensions` in the stack entry.
//  - The issue is that this would make all dependent enums non-copy as well.

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct GenericArrayType<N: Network, const MAX_DIMENSIONS: u8> {
    /// The element type.
    element_type: ElementType<N>,
    /// The dimensions of the array.
    dimensions: [u32; 32],
    /// The number of dimensions of the array.
    num_dimensions: u8,
}

impl<N: Network, const MAX_DIMENSIONS: u8> GenericArrayType<N, MAX_DIMENSIONS> {
    /// Constructs a new array type.
    // Note: `dimensions` needs to be explicitly specified since Rust does not yet support generic parameters in const operations.
    pub fn new(element_type: ElementType<N>, dimensions: [u32; 32], num_dimensions: u8) -> Result<Self> {
        ensure!(num_dimensions != 0, "Cannot have an empty array");
        ensure!(num_dimensions <= MAX_DIMENSIONS, "Cannot exceed the maximum data depth of 32");
        for dimension in &dimensions {
            ensure!(*dimension != 0, "Cannot have an array dimension of zero")
        }
        // TODO (d0cd): Should each dimension of the array be restricted to N::MAX_DATA_ENTRIES?
        //  Initial thoughts are no since it feels restrictive, but we may have to do this due to the merklization.

        Ok(Self { element_type, dimensions, num_dimensions })
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
        // Note the unwrap is safe since `GenericArrayType` must have at least one element in `self.dimensions`.
        *self.dimensions.last().unwrap()
    }
}
