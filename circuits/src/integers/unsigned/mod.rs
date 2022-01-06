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

use crate::{boolean::Boolean, traits::*, Environment, Mode};
use snarkvm_curves::{AffineCurve, TwistedEdwardsParameters};
use snarkvm_fields::Field as F;

use num_traits::{AsPrimitive, Bounded, One, PrimInt, Unsigned as NumUnsigned, Zero};
use std::{
    fmt,
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub type U8<E> = Unsigned<E, u8, 8>;
pub type U16<E> = Unsigned<E, u16, 16>;
pub type U32<E> = Unsigned<E, u32, 32>;
pub type U64<E> = Unsigned<E, u64, 64>;
pub type U128<E> = Unsigned<E, u128, 128>;

#[derive(Clone)]
pub struct Unsigned<E: Environment, I, const SIZE: usize> {
    bits_le: Vec<Boolean<E>>,
    phantom: PhantomData<I>,
}

impl<E: Environment, I, const SIZE: usize> Unsigned<E, I, SIZE>
where
    I: 'static + PrimInt + NumUnsigned + Bounded + Zero + One,
    bool: AsPrimitive<I>,
{
    /// Initializes a new unsigned integer.
    pub fn new(mode: Mode, value: I) -> Self {
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

    /// Returns `true` if the unsigned integer is a constant.
    pub fn is_constant(&self) -> bool {
        self.bits_le.iter().all(|bit| bit.is_constant() == true)
    }

    /// Ejects the unsigned integer as a constant unsigned integer value.
    pub fn eject_value(&self) -> I {
        self.bits_le
            .iter()
            .rev()
            .fold(I::zero(), |value, bit| (value << 1) ^ bit.eject_value().as_())
    }
}

impl<E: Environment, I, const SIZE: usize> fmt::Debug for Unsigned<E, I, SIZE>
where
    I: 'static + PrimInt + NumUnsigned + Bounded + Zero + One + fmt::Display,
    bool: AsPrimitive<I>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Circuit;

    #[test]
    fn test_u8() {
        for i in u8::MIN..=u8::MAX {
            let integer = U8::<Circuit>::new(Mode::Constant, i);
            assert_eq!(integer.eject_value(), i);
        }
    }
}
