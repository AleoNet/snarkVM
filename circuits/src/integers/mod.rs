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

// pub mod add;
// pub mod double;
// pub mod equal;
// pub mod inv;
// pub mod mul;
// pub mod neg;
// pub mod one;
// pub mod sub;
// pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, Field, Mode};
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field as F, One as O, Zero as Z};

// use num_traits::Inv;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub type I8<E> = Signed<E, i8, 8>;
pub type I16<E> = Signed<E, i16, 16>;
pub type I32<E> = Signed<E, i32, 32>;
pub type I64<E> = Signed<E, i64, 64>;
pub type I128<E> = Signed<E, i128, 128>;

#[derive(Clone)]
pub struct Signed<E: Environment, I, const SIZE: usize> {
    bits_le: Vec<Boolean<E>>,
}

impl<E: Environment, I, const SIZE: usize> Signed<E, I, SIZE> {
    /// Initializes a new signed integer.
    pub fn new(mode: Mode, value: I) -> Self {
        // // Derive the y-coordinate if it is not given.
        // let y = match y {
        //     Some(y) => y,
        //     None => E::recover_from_x_coordinate(x).to_y_coordinate(),
        // };
        //
        // // Initialize the x- and y-coordinate field elements.
        // let x = Field::new(mode, x);
        // let y = Field::new(mode, y);

        // Self::from(x, y)
    }

    pub fn to_value(&self) -> (E::BaseField, E::BaseField) {
        // (self.x.to_value(), self.y.to_value())
    }
}
