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

use crate::bits::Boolean;

use std::fmt::Debug;

/// The interface for a singed or unsigned integer gadget.
pub trait Integer: Debug + Clone {
    type IntegerType;
    type UnsignedGadget;
    type UnsignedIntegerType;

    const SIZE: usize;
    const SIGNED: bool;

    fn constant(value: Self::IntegerType) -> Self;

    fn one() -> Self;

    fn zero() -> Self;

    fn new(bits: Vec<Boolean>, value: Option<Self::IntegerType>) -> Self;

    /// Returns true if all bits in this `Int` are constant
    fn is_constant(&self) -> bool;

    /// Returns true if both `Int` objects have constant bits
    fn result_is_constant(first: &Self, second: &Self) -> bool {
        first.is_constant() && second.is_constant()
    }

    fn to_bits_le(&self) -> Vec<Boolean>;

    fn from_bits_le(bits: &[Boolean]) -> Self;

    fn get_value(&self) -> Option<String>;

    fn cast<Target: Integer>(&self) -> Target {
        let bits = self.to_bits_le();
        // let bits_len = bits.len();

        if Target::SIZE <= Self::SIZE {
            // if bits[bits_len..].contains()

            Target::from_bits_le(&bits[0..Target::SIZE])
        } else {
            let mut bits = bits;
            if Self::SIGNED {
                let last_bit = bits[bits.len() - 1].clone();
                for _ in Self::SIZE..Target::SIZE {
                    bits.push(last_bit.clone());
                }
            } else {
                for _ in Self::SIZE..Target::SIZE {
                    bits.push(Boolean::Constant(false));
                }
            }
            Target::from_bits_le(&bits[0..Target::SIZE])
        }
    }
}
