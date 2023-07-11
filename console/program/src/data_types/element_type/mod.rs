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

use crate::{Identifier, LiteralType};
use snarkvm_console_network::prelude::*;

/// An `ElementType` defines the type parameter for an element in an `Array` or `Vector`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum ElementType<N: Network> {
    /// A literal element type.
    Literal(LiteralType),
    /// A struct element type.
    Struct(Identifier<N>),
}

impl<N: Network> From<LiteralType> for ElementType<N> {
    /// Initializes an element type from a literal type.
    fn from(literal: LiteralType) -> Self {
        ElementType::Literal(literal)
    }
}

impl<N: Network> From<Identifier<N>> for ElementType<N> {
    /// Initializes an element type from a struct type.
    fn from(struct_: Identifier<N>) -> Self {
        ElementType::Struct(struct_)
    }
}
