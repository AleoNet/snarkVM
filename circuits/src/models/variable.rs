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

use crate::models::*;
use snarkvm_fields::traits::*;

use std::ops::{Add, AddAssign, Neg, Sub};

pub type Index = u64;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Variable<F: PrimeField> {
    Constant(F),
    Public(Index, F),
    Private(Index, F),
}

impl<F: PrimeField> Variable<F> {
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Constant(..) => true,
            _ => false,
        }
    }

    pub fn is_public(&self) -> bool {
        match self {
            Self::Public(..) => true,
            _ => false,
        }
    }

    pub fn is_private(&self) -> bool {
        match self {
            Self::Private(..) => true,
            _ => false,
        }
    }

    pub fn one() -> Self {
        Self::Public(0, F::one())
    }

    pub fn value(&self) -> F {
        match self {
            Self::Constant(value) => *value,
            Self::Public(_, value) => *value,
            Self::Private(_, value) => *value,
        }
    }
}

// impl<F: PrimeField> Add<Self> for Variable<F> {
//     type Output = LinearCombination<F>;
//
//     fn add(self, other: Self) -> Self::Output {
//         match (self, other) {
//             (Self::Constant(a), Self::Constant(b)) => Self::Constant(a + b).into(),
//             (first, second) => LinearCombination::from([first, second]),
//         }
//     }
// }
//
// impl<F: PrimeField> Sub<Self> for Variable<F> {
//     type Output = LinearCombination<F>;
//
//     fn sub(self, other: Self) -> Self::Output {
//         match (self, other) {
//             (Self::Constant(a), Self::Constant(b)) => Self::Constant(a - b).into(),
//             (first, second) => LinearCombination::from(first) - second,
//         }
//     }
// }
