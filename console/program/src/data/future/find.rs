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

use super::*;

impl<N: Network> Future<N> {
    /// Returns a value from the given path.
    pub fn find<A: Into<Access<N>> + Copy + Debug>(&self, path: &[A]) -> Result<Value<N>> {
        // Ensure the path is not empty.
        ensure!(!path.is_empty(), "Attempted to find an argument with an empty path.");

        // Initialize a value starting from the top-level.
        let mut value = None;

        // Iterate through the path to retrieve the value.
        for access in path.iter() {
            let index = match (*access).into() {
                Access::Member(identifier) => {
                    bail!("Attempted to find an argument to the future with the member access '{identifier}'")
                }
                Access::Index(index) => index,
            };

            match self.arguments.get(*index as usize) {
                // Retrieve the argument and update `value` for the next iteration.
                Some(argument) => value = Some(argument),
                // Halts if the index is out of bounds.
                None => bail!("Index '{index}' is out of bounds"),
            }
        }

        match value {
            Some(Argument::Plaintext(plaintext)) => Ok(Value::Plaintext(plaintext.clone())),
            Some(Argument::Future(future)) => Ok(Value::Future(future.clone())),
            None => bail!("Failed to locate argument"),
        }
    }
}
