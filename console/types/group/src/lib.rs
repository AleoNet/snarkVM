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

mod arithmetic;
mod from_bits;
mod from_x_coordinate;
mod from_xy_coordinate;
mod parse;
mod random;
mod size_in_bits;
mod to_bits;
mod to_x_coordinate;
mod to_y_coordinate;
mod zero;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_scalar::Scalar;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Group<E: Environment> {
    /// The underlying group element.
    group: E::Projective,
}

impl<E: Environment> GroupTrait<Scalar<E>> for Group<E> {}

impl<E: Environment> Group<E> {
    /// Initializes a new group.
    pub fn new(group: E::Affine) -> Self {
        Self { group: group.into() }
    }

    /// Returns the prime subgroup generator.
    pub fn generator() -> Self {
        Self { group: E::Affine::prime_subgroup_generator().to_projective() }
    }

    /// Returns `self * COFACTOR`.
    pub fn mul_by_cofactor(&self) -> Self {
        // (For advanced users) The cofactor for this curve is `4`. Thus doubling is used to be performant.
        // See unit tests below, which sanity check that this condition holds.
        debug_assert!(E::Affine::cofactor().len() == 1 && E::Affine::cofactor()[0] == 4);

        Self { group: self.group.double().double() }
    }
}

impl<E: Environment> Group<E> {
    /// This internal function initializes a group element from projective coordinates.
    const fn from_projective(group: E::Projective) -> Self {
        Self { group }
    }
}

impl<E: Environment> TypeName for Group<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "group"
    }
}

impl<E: Environment> Deref for Group<E> {
    type Target = E::Projective;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.group
    }
}
