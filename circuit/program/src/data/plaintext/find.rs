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

impl<A: Aleo> Plaintext<A> {
    /// Returns the plaintext member from the given path.
    pub fn find(&self, path: &[Identifier<A>]) -> Result<Plaintext<A>> {
        // Ensure the path is not empty.
        if path.is_empty() {
            A::halt("Attempted to find member with an empty path.")
        }

        match self {
            // Halts if the value is not a struct.
            Self::Literal(..) => A::halt("Literal is not a struct"),
            // Retrieve the value of the member (from the value).
            Self::Struct(members, ..) => {
                // Initialize the members starting from the top-level.
                let mut submembers = members;

                // Initialize the output.
                let mut output = None;

                // Iterate through the path to retrieve the value.
                for (i, identifier) in path.iter().enumerate() {
                    // If this is not the last item in the path, ensure the value is a struct.
                    if i != path.len() - 1 {
                        match submembers.get(identifier) {
                            // Halts if the member is not a struct.
                            Some(Self::Literal(..)) => bail!("'{identifier}' must be a struct"),
                            // Retrieve the member and update `submembers` for the next iteration.
                            Some(Self::Struct(members, ..)) => submembers = members,
                            // Halts if the member does not exist.
                            None => bail!("Failed to locate member '{identifier}' in struct"),
                        }
                    }
                    // Otherwise, return the final member.
                    else {
                        match submembers.get(identifier) {
                            // Return the plaintext member.
                            Some(plaintext) => output = Some(plaintext.clone()),
                            // Halts if the member does not exist.
                            None => bail!("Failed to locate member '{identifier}' in struct"),
                        }
                    }
                }

                // Return the output.
                match output {
                    Some(output) => Ok(output),
                    None => A::halt("Failed to locate member in struct from path"),
                }
            }
        }
    }
}
