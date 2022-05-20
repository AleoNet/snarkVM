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

use std::borrow::Cow;

impl<E: Environment, const WINDOW_SIZE: usize, const NUM_WINDOWS: usize> HashUncompressed
    for Sinsemilla<E, WINDOW_SIZE, NUM_WINDOWS>
{
    type Input = Boolean<E>;
    type Output = Group<E>;

    fn hash_uncompressed(&self, input: &[Self::Input]) -> Self::Output {
        // Ensure the input size is within the size bounds.
        let mut input = Cow::Borrowed(input);
        match input.len() <= NUM_WINDOWS * WINDOW_SIZE {
            // Pad the input if it is under the required parameter size.
            true => input.to_mut().resize(WINDOW_SIZE * NUM_WINDOWS, Boolean::constant(false)),
            // Ensure the input size is within the parameter size.
            false => E::halt(format!("The Sinsemilla hash input cannot exceed {} bits.", WINDOW_SIZE * NUM_WINDOWS)),
        }

        input.chunks(WINDOW_SIZE).fold(self.q.clone(), |acc, bits| {
            let q = acc.double();
            // TODO: lookup from bit combination
            q
        })
    }
}
