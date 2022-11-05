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

impl<E: Environment> Group<E> {
    /// Initializes a new group from the `(x, y)` affine coordinates.
    pub fn from_xy_coordinates(x: Field<E>, y: Field<E>) -> Self {
        match E::Affine::from_coordinates((*x, *y)) {
            Some(point) => Self { group: point.into() },
            None => E::halt("Attempted to recover an invalid group element from (x, y) coordinates"),
        }
    }

    /// Initializes a new group from the `(x, y)` affine coordinates.
    /// Note: The resulting point is **not** enforced to be on the curve or in the subgroup.
    pub fn from_xy_coordinates_unchecked(x: Field<E>, y: Field<E>) -> Self {
        Self { group: E::Affine::from_coordinates_unchecked((*x, *y)).into() }
    }
}
