// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::curves::PrimeField;
use snarkvm_utilities::{
    bititerator::BitIteratorBE,
    bytes::{FromBytes, ToBytes},
    rand::UniformRand,
};

use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

use crate::curves::Zero;

pub trait Group:
    ToBytes
    + FromBytes
    + Copy
    + Clone
    + Debug
    + Display
    + Default
    + Send
    + Sync
    + 'static
    + Eq
    + Hash
    + Neg<Output = Self>
    + UniformRand
    + Zero
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
{
    type ScalarField: PrimeField + Into<<Self::ScalarField as PrimeField>::BigInteger>;

    /// Returns `self + self`.
    #[must_use]
    fn double(&self) -> Self;

    /// Sets `self := self + self`.
    fn double_in_place(&mut self) -> &mut Self;

    #[must_use]
    fn mul(&self, other: &Self::ScalarField) -> Self {
        let mut copy = *self;
        copy.mul_assign(other);
        copy
    }

    fn mul_assign(&mut self, other: &Self::ScalarField) {
        let mut res = Self::zero();
        for i in BitIteratorBE::new(other.into_repr()) {
            res.double_in_place();
            if i {
                res += self;
            }
        }
        *self = res
    }
}
