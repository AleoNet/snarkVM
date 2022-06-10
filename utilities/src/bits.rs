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

use crate::Vec;

use anyhow::Result;

pub trait ToBits: Sized {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> Vec<bool>;

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> Vec<bool>;
}

pub trait FromBits: Sized {
    /// Reads `Self` from a boolean array in little-endian order.
    fn from_bits_le(bits: &[bool]) -> Result<Self>;

    /// Reads `Self` from a boolean array in big-endian order.
    fn from_bits_be(bits: &[bool]) -> Result<Self>;
}

pub trait ToMinimalBits: Sized {
    /// Returns `self` as a minimal boolean array.
    fn to_minimal_bits(&self) -> Vec<bool>;
}

impl<T: ToMinimalBits> ToMinimalBits for Vec<T> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        let mut res_bits = vec![];
        for elem in self.iter() {
            res_bits.extend(elem.to_minimal_bits());
        }
        res_bits
    }
}

/********************/
/****** Tuples ******/
/********************/

/// A helper macro to implement `ToBits` for a tuple of `ToBits` circuits.
macro_rules! to_bits_tuple {
    (($t0:ident, $i0:tt), $(($ty:ident, $idx:tt)),+) => {
        impl<$t0: ToBits, $($ty: ToBits),+> ToBits for ($t0, $($ty),+) {
            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le(&self) -> Vec<bool> {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_le().into_iter()
                    $(.chain(self.$idx.to_bits_le().into_iter()))+
                    .collect()
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be(&self) -> Vec<bool> {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_be().into_iter()
                    $(.chain(self.$idx.to_bits_be().into_iter()))+
                    .collect()
            }
        }

        impl<'a, $t0: ToBits, $($ty: ToBits),+> ToBits for &'a ($t0, $($ty),+) {
            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le(&self) -> Vec<bool> {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_le().into_iter()
                    $(.chain(self.$idx.to_bits_le().into_iter()))+
                    .collect()
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be(&self) -> Vec<bool> {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_be().into_iter()
                    $(.chain(self.$idx.to_bits_be().into_iter()))+
                    .collect()
            }
        }
    }
}

to_bits_tuple!((C0, 0), (C1, 1));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8), (C9, 9));
to_bits_tuple!((C0, 0), (C1, 1), (C2, 2), (C3, 3), (C4, 4), (C5, 5), (C6, 6), (C7, 7), (C8, 8), (C9, 9), (C10, 10));

/********************/
/***** Integers *****/
/********************/

macro_rules! impl_bits_for_integer {
    ($int:ty) => {
        impl ToBits for $int {
            /// Returns `self` as a boolean array in little-endian order.
            #[inline]
            fn to_bits_le(&self) -> Vec<bool> {
                let mut bits_le = Vec::with_capacity(<$int>::BITS as usize);
                let mut value = self.to_le();
                for _ in 0..<$int>::BITS {
                    bits_le.push(value & 1 == 1);
                    value = value.wrapping_shr(1u32);
                }
                bits_le
            }

            /// Returns `self` as a boolean array in big-endian order.
            #[inline]
            fn to_bits_be(&self) -> Vec<bool> {
                self.to_bits_le().into_iter().rev().collect()
            }
        }

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
/****** String ******/
/********************/

impl ToBits for String {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<bool> {
        // The vector is order-preserving, meaning the first byte in is the first byte bits out.
        self.as_bytes().to_bits_le()
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<bool> {
        // The vector is order-preserving, meaning the first byte in is the first byte bits out.
        self.as_bytes().to_bits_be()
    }
}

/********************/
/****** Arrays ******/
/********************/

impl<C: ToBits> ToBits for Vec<C> {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<bool> {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_le()
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<bool> {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_be()
    }
}

impl<C: ToBits, const N: usize> ToBits for [C; N] {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<bool> {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_le()
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<bool> {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_be()
    }
}

impl<C: ToBits> ToBits for &[C] {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le(&self) -> Vec<bool> {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.iter().flat_map(|c| c.to_bits_le()).collect()
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be(&self) -> Vec<bool> {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.iter().flat_map(|c| c.to_bits_be()).collect()
    }
}

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
                    let expected: $integer = Uniform::rand(&mut test_rng());

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
