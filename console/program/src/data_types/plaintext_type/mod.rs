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

/// A `ValueType` defines the type parameter for an entry in an `Struct`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum PlaintextType<N: Network> {
    /// A literal type contains its type name.
    /// The format of the type is `<type_name>`.
    Literal(LiteralType),
    /// An struct type contains its identifier.
    /// The format of the type is `<identifier>`.
    Struct(Identifier<N>),
}

impl<N: Network> From<LiteralType> for PlaintextType<N> {
    /// Initializes a plaintext type from a literal type.
    fn from(literal: LiteralType) -> Self {
        PlaintextType::Literal(literal)
    }
}

impl<N: Network> From<Identifier<N>> for PlaintextType<N> {
    /// Initializes a plaintext type from a struct type.
    fn from(struct_: Identifier<N>) -> Self {
        PlaintextType::Struct(struct_)
    }
}
