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

use super::*;

impl<N: Network> Value<N, Plaintext<N>> {
    /// Returns the value from the given path.
    pub fn find(&self, path: &[Identifier<N>]) -> Result<Value<N, Plaintext<N>>> {
        match self {
            Value::Constant(plaintext) => Ok(Value::Constant(plaintext.find(path)?)),
            Value::Public(plaintext) => Ok(Value::Public(plaintext.find(path)?)),
            Value::Private(plaintext) => Ok(Value::Private(plaintext.find(path)?)),
            Value::Record(record) => Ok(Value::from(record.find(path)?)),
        }
    }
}
