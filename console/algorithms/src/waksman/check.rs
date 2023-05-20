// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<E: Environment> ASWaksman<E> {
    /// Returns `true` if `first` is a permutation of `second`, given the `selectors` for the switches in the network.
    pub fn check_permutation(&self, first: &[Field<E>], second: &[Field<E>], selectors: &[Boolean<E>]) -> Boolean<E> {
        // Check that the two sequences are the same length.
        if first.len() != second.len() {
            return E::halt("The two sequences must be the same length.");
        }

        // Run the network on the first sequence, using the given selectors.
        let output = self.run(first, selectors);

        // Check that the output of the network is element-wise equal to the second sequence.
        output.iter().zip_eq(second).fold(Boolean::new(true), |acc, (a, b)| acc & a.is_equal(b))
    }
}
