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
pub mod neg;
pub mod one;
pub mod sub;
pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, LinearCombination, Mode, Variable};
// use snarkvm_fields::Field as F;
use snarkvm_fields::{One as O, Zero as Z};

use anyhow::Result;
use std::ops::{Add, AddAssign, Div, Mul, Neg, Sub, SubAssign};

pub struct Field<E: Environment>(LinearCombination<E::Field>);

impl<E: Environment> Field<E> {
    pub fn new(mode: Mode, value: E::Field) -> Self {
        match mode {
            Mode::Constant => Self(E::new_constant(value).into()),
            Mode::Public => Self(E::new_public(value).into()),
            Mode::Private => Self(E::new_private(value).into()),
        }
    }

    pub fn to_value(&self) -> E::Field {
        self.0.to_value()
    }
}
