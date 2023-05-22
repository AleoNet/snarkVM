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
mod equal;
mod find;
mod parse;
mod serialize;
mod to_bits;
mod to_fields;

use crate::{Entry, Identifier, Plaintext, Record};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Clone)]
pub enum Value<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value.
    Record(Record<N, Plaintext<N>>),
}

impl<N: Network> From<&Value<N>> for Value<N> {
    /// Returns a clone of the value.
    fn from(value: &Value<N>) -> Self {
        value.clone()
    }
}

impl<N: Network> TryFrom<Result<Value<N>>> for Value<N> {
    type Error = Error;

    /// Initializes a value from a result.
    fn try_from(value: Result<Value<N>>) -> Result<Self> {
        value
    }
}

impl<N: Network> TryFrom<String> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: String) -> Result<Self> {
        Self::from_str(&value)
    }
}

impl<N: Network> TryFrom<&String> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &String) -> Result<Self> {
        Self::from_str(value)
    }
}

impl<N: Network> TryFrom<&str> for Value<N> {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &str) -> Result<Self> {
        Self::from_str(value)
    }
}
