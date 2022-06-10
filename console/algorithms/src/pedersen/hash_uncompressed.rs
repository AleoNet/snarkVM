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

impl<E: Environment, const NUM_BITS: u8> HashUncompressed for Pedersen<E, NUM_BITS> {
    type Input = bool;
    type Output = Group<E>;

    /// Returns the Pedersen hash of the given input as a group element.
    fn hash_uncompressed(&self, input: &[Self::Input]) -> Result<Self::Output> {
        let mut input = Cow::Borrowed(input);
        match input.len() <= NUM_BITS as usize {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(NUM_BITS as usize, false),
            // Ensure the input size is within the parameter size,
            false => bail!("Invalid input size for Pedersen: expected <= {NUM_BITS}, found {}", input.len()),
        }

        // Compute sum of h_i^{m_i} for all i.
        Ok(input
            .iter()
            .zip_eq(&*self.base_window)
            .flat_map(|(bit, base)| match bit {
                true => Some(*base),
                false => None,
            })
            .sum())
    }
}
