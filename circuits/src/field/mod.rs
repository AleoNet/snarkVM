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

pub mod add;
pub mod inv;
pub mod mul;
pub mod neg;
pub mod one;
pub mod sub;
pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, LinearCombination, Mode, Variable};
use snarkvm_fields::{Field as F, One as O, Zero as Z};

use anyhow::Result;
use num_traits::Inv;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

pub struct Field<E: Environment>(LinearCombination<E::Field>);

impl<E: Environment> Field<E> {
    pub fn new(mode: Mode, value: E::Field) -> Self {
        Self(E::new_variable(mode, value).into())
    }

    pub fn to_value(&self) -> E::Field {
        self.0.to_value()
    }
}

impl<E: Environment> From<Field<E>> for LinearCombination<E::Field> {
    fn from(field: Field<E>) -> Self {
        field.0
    }
}

impl<E: Environment> From<&Field<E>> for LinearCombination<E::Field> {
    fn from(field: &Field<E>) -> Self {
        field.0.clone()
    }
}
