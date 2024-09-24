// Copyright 2024 Aleo Network Foundation
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

use crate::{EntryType, Identifier, Locator, PlaintextType};
use snarkvm_console_network::prelude::*;

use enum_index::EnumIndex;

#[derive(Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum ValueType<N: Network> {
    /// A constant type.
    Constant(PlaintextType<N>),
    /// A publicly-visible type.
    Public(PlaintextType<N>),
    /// A private type decrypted with the account owner's address.
    Private(PlaintextType<N>),
    /// A record type inherits its visibility from the record definition.
    Record(Identifier<N>),
    /// An external record type inherits its visibility from its record definition.
    ExternalRecord(Locator<N>),
    /// A publicly-visible future.
    Future(Locator<N>),
}

impl<N: Network> From<EntryType<N>> for ValueType<N> {
    fn from(entry: EntryType<N>) -> Self {
        match entry {
            EntryType::Constant(plaintext) => ValueType::Constant(plaintext),
            EntryType::Public(plaintext) => ValueType::Public(plaintext),
            EntryType::Private(private) => ValueType::Private(private),
        }
    }
}
