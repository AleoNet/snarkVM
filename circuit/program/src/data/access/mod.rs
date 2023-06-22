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

use crate::Identifier;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{Eject, Inject, Mode, U32};

/// A register `Access`.
#[derive(Clone)]
pub enum Access<A: Aleo> {
    /// The access is an index.
    Index(U32<A>),
    /// The access is a member.
    Member(Identifier<A>),
}

#[cfg(console)]
impl<A: Aleo> Inject for Access<A> {
    type Primitive = console::Access<A::Network>;

    /// Initializes a new access circuit from a primitive.
    fn new(mode: Mode, plaintext: Self::Primitive) -> Self {
        match plaintext {
            Self::Primitive::Index(index) => Self::Index(U32::new(mode, index)),
            Self::Primitive::Member(identifier) => Self::Member(Identifier::new(mode, identifier)),
        }
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for Access<A> {
    type Primitive = console::Access<A::Network>;

    /// Ejects the mode of the access.
    fn eject_mode(&self) -> Mode {
        match self {
            Self::Index(index) => index.eject_mode(),
            Self::Member(member) => member.eject_mode(),
        }
    }

    /// Ejects the access.
    fn eject_value(&self) -> Self::Primitive {
        match self {
            Self::Index(index) => console::Access::Index(index.eject_value()),
            Self::Member(identifier) => console::Access::Member(identifier.eject_value()),
        }
    }
}
