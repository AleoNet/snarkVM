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
