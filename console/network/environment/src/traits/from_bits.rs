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

use anyhow::Result;

pub trait FromBits: Sized {
    /// Reads `Self` from a boolean array in little-endian order.
    fn from_bits_le(bits: &[bool]) -> Result<Self>;

    /// Reads `Self` from a boolean array in big-endian order.
    fn from_bits_be(bits: &[bool]) -> Result<Self>;
}

/********************/
/***** Integers *****/
/********************/

macro_rules! impl_bits_for_integer {
    ($int:ty) => {
        impl FromBits for $int {
            /// Reads `Self` from a boolean array in little-endian order.
            #[inline]
            fn from_bits_le(bits: &[bool]) -> Result<Self> {
                Ok(bits.iter().rev().fold(0, |value, bit| match bit {
                    true => (value.wrapping_shl(1)) ^ 1,
                    false => (value.wrapping_shl(1)) ^ 0,
                }))
            }

            /// Reads `Self` from a boolean array in big-endian order.
            #[inline]
            fn from_bits_be(bits: &[bool]) -> Result<Self> {
                Self::from_bits_le(&bits.iter().rev().copied().collect::<Vec<_>>())
            }
        }
    };
}

impl_bits_for_integer!(u8);
impl_bits_for_integer!(u16);
impl_bits_for_integer!(u32);
impl_bits_for_integer!(u64);
impl_bits_for_integer!(u128);

impl_bits_for_integer!(i8);
impl_bits_for_integer!(i16);
impl_bits_for_integer!(i32);
impl_bits_for_integer!(i64);
impl_bits_for_integer!(i128);

/********************/
/****** Arrays ******/
/********************/

impl FromBits for Vec<u8> {
    /// A helper method to return `Self` from a concatenated list of little-endian bits.
    #[inline]
    fn from_bits_le(bits: &[bool]) -> Result<Self> {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        bits.chunks(8).map(u8::from_bits_le).collect::<Result<Vec<_>>>()
    }

    /// A helper method to return `Self` from a concatenated list of big-endian bits.
    #[inline]
    fn from_bits_be(bits: &[bool]) -> Result<Self> {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        bits.chunks(8).map(u8::from_bits_be).collect::<Result<Vec<_>>>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 10000;

    #[test]
    fn test_integers() -> Result<()> {
        macro_rules! check_integer {
            ($integer:tt) => {{
                for _ in 0..ITERATIONS {
                    let expected: $integer = UniformRand::rand(&mut test_rng());

                    let bits_le = expected.to_bits_le();
                    assert_eq!(expected, $integer::from_bits_le(&bits_le)?);

                    let bits_be = expected.to_bits_be();
                    assert_eq!(expected, $integer::from_bits_be(&bits_be)?);
                }
            }};
        }

        check_integer!(u8);
        check_integer!(u16);
        check_integer!(u32);
        check_integer!(u64);
        check_integer!(u128);

        check_integer!(i8);
        check_integer!(i16);
        check_integer!(i32);
        check_integer!(i64);
        check_integer!(i128);

        Ok(())
    }
}
