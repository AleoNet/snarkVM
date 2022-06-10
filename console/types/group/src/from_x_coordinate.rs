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
    /// Attempts to recover an affine group element from a given x-coordinate field element.
    /// For safety, the resulting point is always enforced to be on the curve and in the correct subgroup.
    pub fn from_x_coordinate(x_coordinate: Field<E>) -> Result<Self> {
        if let Some(point) = E::Affine::from_x_coordinate(*x_coordinate, true) {
            if point.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self::new(point));
            }
        }
        if let Some(point) = E::Affine::from_x_coordinate(*x_coordinate, false) {
            if point.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(Self::new(point));
            }
        }
        bail!("Failed to recover an affine group from an x-coordinate of {x_coordinate}")
    }
}
