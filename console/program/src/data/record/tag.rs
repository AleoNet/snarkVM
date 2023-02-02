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
    /// A helper method to derive the tag from the `sk_tag` and commitment.
    pub fn tag(sk_tag: Field<N>, commitment: Field<N>) -> Result<Field<N>> {
        // Compute the tag as `Hash(sk_tag, commitment)`.
        N::hash_psd2(&[sk_tag, commitment])
    }
}
