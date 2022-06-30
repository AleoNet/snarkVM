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

impl<N: Network, Private: Visibility> Record<N, Private> {
    /// Returns the number of field elements to encode `self`.
    pub(crate) fn num_randomizers(&self) -> Result<u16> {
        // Initialize an tracker for the number of randomizers.
        let mut num_randomizers: u16 = 0;

        // If the owner is private, increment the number of randomizers by 1.
        if self.owner.is_private() {
            num_randomizers += 1;
        }

        // If the balance is private, increment the number of randomizers by 1.
        if self.balance.is_private() {
            num_randomizers += 1;
        }

        // Increment the number of randomizers by the number of data randomizers.
        for (_, entry) in self.data.iter() {
            num_randomizers = num_randomizers
                .checked_add(entry.num_randomizers()?)
                .ok_or_else(|| anyhow!("Number of randomizers exceeds maximum allowed size."))?;
        }

        // Ensure the number of randomizers does not exceed the maximum allowed size.
        match num_randomizers as u32 <= N::MAX_DATA_SIZE_IN_FIELDS {
            true => Ok(num_randomizers),
            false => bail!("Number of randomizers exceeds the maximum allowed size."),
        }
    }
}
