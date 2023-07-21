// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::Vec;

use anyhow::Result;

pub trait ToBitsInto: Sized {
    /// Converts `self` to booleans moved into the given vector in
    /// little-endian order.
    fn to_bits_le_into(&self, _vec: &mut Vec<bool>);

    /// Converts `self` to booleans moved into the given vector in
    /// big-endian order.
    fn to_bits_be_into(&self, _vec: &mut Vec<bool>);
}

pub trait ToBits: Sized + ToBitsInto {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> Vec<bool>;

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> Vec<bool>;
}

impl<T: ToBitsInto> ToBits for T {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> Vec<bool> {
        let mut vec = vec![];
        self.to_bits_le_into(&mut vec);
        vec
    }

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> Vec<bool> {
        let mut vec = vec![];
        self.to_bits_be_into(&mut vec);
        vec
    }
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

/// A helper macro to implement `ToBitsInto` for a tuple of `ToBitsInto` circuits.
macro_rules! to_bits_tuple {
    (($t0:ident, $i0:tt), $(($ty:ident, $idx:tt)),+) => {
        impl<$t0: ToBitsInto, $($ty: ToBitsInto),+> ToBitsInto for ($t0, $($ty),+) {
            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                (&self).to_bits_le_into(vec);
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                (&self).to_bits_be_into(vec);
            }
        }

        impl<'a, $t0: ToBitsInto, $($ty: ToBitsInto),+> ToBitsInto for &'a ($t0, $($ty),+) {
            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_le_into(vec);
                $(self.$idx.to_bits_le_into(vec);)+
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_be_into(vec);
                $(self.$idx.to_bits_be_into(vec);)+
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
        impl ToBitsInto for $int {
            /// Returns `self` as a boolean array in little-endian order.
            #[inline]
            fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
                vec.reserve(<$int>::BITS as usize);
                let mut value = *self;
                for _ in 0..<$int>::BITS {
                    vec.push(value & 1 == 1);
                    value = value.wrapping_shr(1u32);
                }
            }

            /// Returns `self` as a boolean array in big-endian order.
            #[inline]
            fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
                let reversed = self.reverse_bits();
                reversed.to_bits_le_into(vec);
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
                Ok(bits.iter().fold(0, |value, bit| match bit {
                    true => (value.wrapping_shl(1)) ^ 1,
                    false => (value.wrapping_shl(1)) ^ 0,
                }))
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

impl ToBitsInto for String {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        self.as_bytes().to_bits_le_into(vec);
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        self.as_bytes().to_bits_be_into(vec);
    }
}

/********************/
/****** Arrays ******/
/********************/

impl<C: ToBitsInto> ToBitsInto for Vec<C> {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_le_into(vec);
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        // The vector is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_be_into(vec);
    }
}

impl<C: ToBitsInto, const N: usize> ToBitsInto for [C; N] {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_le_into(vec);
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        self.as_slice().to_bits_be_into(vec);
    }
}

impl<C: ToBitsInto> ToBitsInto for &[C] {
    /// A helper method to return a concatenated list of little-endian bits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        for elem in self.iter() {
            elem.to_bits_le_into(vec);
        }
    }

    /// A helper method to return a concatenated list of big-endian bits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        // The slice is order-preserving, meaning the first variable in is the first variable bits out.
        for elem in self.iter() {
            elem.to_bits_be_into(vec);
        }
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
    use crate::{TestRng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 10000;

    #[test]
    fn test_integers() -> Result<()> {
        macro_rules! check_integer {
            ($integer:tt, $rng:expr) => {{
                for _ in 0..ITERATIONS {
                    let expected: $integer = Uniform::rand($rng);

                    let bits_le = expected.to_bits_le();
                    assert_eq!(expected, $integer::from_bits_le(&bits_le)?);

                    let bits_be = expected.to_bits_be();
                    assert_eq!(expected, $integer::from_bits_be(&bits_be)?);
                }
            }};
        }

        let mut rng = TestRng::default();

        check_integer!(u8, &mut rng);
        check_integer!(u16, &mut rng);
        check_integer!(u32, &mut rng);
        check_integer!(u64, &mut rng);
        check_integer!(u128, &mut rng);

        check_integer!(i8, &mut rng);
        check_integer!(i16, &mut rng);
        check_integer!(i32, &mut rng);
        check_integer!(i64, &mut rng);
        check_integer!(i128, &mut rng);

        Ok(())
    }
}
