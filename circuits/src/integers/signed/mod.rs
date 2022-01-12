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
// pub mod double;
pub mod equal;
pub mod less_than;
// pub mod inv;
pub mod div;
pub mod mul;
//pub mod pow;
pub mod neg;
// pub mod one;
pub mod sub;
pub mod ternary;
// pub mod zero;

use crate::{boolean::Boolean, traits::*, Environment, Mode, PrimitiveSignedInteger};

use std::{
    fmt,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub type I8<E> = Signed<E, i8, 8>;
pub type I16<E> = Signed<E, i16, 16>;
pub type I32<E> = Signed<E, i32, 32>;
pub type I64<E> = Signed<E, i64, 64>;
pub type I128<E> = Signed<E, i128, 128>;

#[derive(Clone)]
pub struct Signed<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> Signed<E, I, SIZE> {
    /// Initializes a new integer.
    pub fn new(mode: Mode, value: I) -> Self {
        if SIZE == 0 {
            E::halt("Signed must have a size greater than zero.")
        }

        let mut bits_le = Vec::with_capacity(SIZE);
        let mut value = value.to_le();
        for _ in 0..SIZE {
            bits_le.push(Boolean::new(mode, value & I::one() == I::one()));
            value = value >> 1;
        }
        Self {
            bits_le,
            phantom: Default::default(),
        }
    }

    // TODO: (@pranav) Implement From?
    /// Initialize a new integer from a vector of Booleans.
    fn from_bits(bits: Vec<Boolean<E>>) -> Self {
        if SIZE == 0 {
            E::halt("Signed must have a size greater than zero.")
        }
        if bits.len() != SIZE {
            E::halt("Incorrect number of bits to convert to Signed")
        }

        Self {
            bits_le: bits,
            phantom: Default::default(),
        }
    }

    /// Returns `true` if the integer is a constant.
    pub fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the signed integer as a constant signed integer value.
    pub fn eject_value(&self) -> I {
        let base = if self.bits_le[SIZE - 1].eject_value() == true {
            I::min_value()
        } else {
            I::zero()
        };

        let mut magnitude = I::zero();

        for i in (0..SIZE - 1).rev() {
            // TODO (@pranav) This explicit cast could be eliminated by using a trait bound
            //  `bool: AsPrimitive<I>`. This however requires the trait bound to be expressed
            //  for every implementation of Signed that uses `eject_value` which looks unclean.
            let bit_value = if self.bits_le[i].eject_value() {
                I::one()
            } else {
                I::zero()
            };
            magnitude = (magnitude << 1) ^ bit_value;
        }

        base + magnitude
    }
}

impl<E: Environment, I: PrimitiveSignedInteger, const SIZE: usize> fmt::Debug for Signed<E, I, SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.eject_value())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_i8() {
        for i in i8::MIN..=i8::MAX {
            let integer = I8::<Circuit>::new(Mode::Constant, i);
            assert_eq!(integer.eject_value(), i);
        }
    }
}
