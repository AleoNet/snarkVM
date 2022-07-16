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

impl<A: Aleo> Record<A, Plaintext<A>> {
    /// Returns the entry from the given path.
    pub fn find(&self, path: &[Identifier<A>]) -> Result<Entry<A, Plaintext<A>>> {
        // If the path is of length one, check if the path is requesting the `owner` or `gates`.
        if path.len() == 1 {
            if path[0] == Identifier::from_str("owner")? {
                return Ok(self.owner.to_entry());
            } else if path[0] == Identifier::from_str("gates")? {
                return Ok(self.gates.to_entry());
            }
        }

        // Ensure the path is not empty.
        if let Some((first, rest)) = path.split_first() {
            // Retrieve the top-level entry.
            match self.data.get(first) {
                Some(entry) => match rest.is_empty() {
                    // If the remaining path is empty, return the top-level entry.
                    true => Ok(entry.clone()),
                    // Otherwise, recursively call `find` on the top-level entry.
                    false => entry.find(rest),
                },
                None => bail!("Record entry `{first}` not found."),
            }
        } else {
            bail!("Attempted to find record entry with an empty path.")
        }
    }
}
