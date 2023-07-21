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

use crate::BooleanTrait;

pub trait ToBitsInto {
    type Boolean: BooleanTrait;

    /// Converts `self` to circuit bits moved into the given vector in
    /// little-endian order.
    fn to_bits_le_into(&self, _vec: &mut Vec<Self::Boolean>);

    /// Converts `self` to circuit bits moved into the given vector in
    /// big-endian order.
    fn to_bits_be_into(&self, _vec: &mut Vec<Self::Boolean>);
}

/// Unary operator for converting to bits.
pub trait ToBits: ToBitsInto {
    /// Returns the little-endian bits of the circuit.
    fn to_bits_le(&self) -> Vec<<Self as ToBitsInto>::Boolean>;

    /// Returns the big-endian bits of the circuit.
    fn to_bits_be(&self) -> Vec<<Self as ToBitsInto>::Boolean>;
}

impl<T: ToBitsInto> ToBits for T {
    /// Returns `self` as a circuit bit array in little-endian order.
    fn to_bits_le(&self) -> Vec<<Self as ToBitsInto>::Boolean> {
        let mut vec = vec![];
        self.to_bits_le_into(&mut vec);
        vec
    }

    /// Returns `self` as a circuit bit array in big-endian order.
    fn to_bits_be(&self) -> Vec<<Self as ToBitsInto>::Boolean> {
        let mut vec = vec![];
        self.to_bits_be_into(&mut vec);
        vec
    }
}

/********************/
/****** Arrays ******/
/********************/

impl<C: ToBitsInto<Boolean = B>, B: BooleanTrait> ToBitsInto for Vec<C> {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The vector is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_le_into(vec);
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The vector is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_be_into(vec);
    }
}

impl<C: ToBitsInto<Boolean = B>, B: BooleanTrait, const N: usize> ToBitsInto for [C; N] {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_le_into(vec);
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_be_into(vec);
    }
}

impl<C: ToBitsInto<Boolean = B>, B: BooleanTrait> ToBitsInto for &[C] {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        for elem in self.iter() {
            elem.to_bits_le_into(vec);
        }
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        for elem in self.iter() {
            elem.to_bits_be_into(vec);
        }
    }
}

/********************/
/****** Tuples ******/
/********************/

/// A helper macro to implement `ToBitsInto` for a tuple of `ToBitsInto` circuits.
macro_rules! to_bits_tuple {
    (($t0:ident, $i0:tt), $(($ty:ident, $idx:tt)),+) => {
        impl<B: BooleanTrait, $t0: ToBitsInto<Boolean = B>, $($ty: ToBitsInto<Boolean = B>),+> ToBitsInto for ($t0, $($ty),+) {
            type Boolean = B;

            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_le_into(vec);
                $(self.$idx.to_bits_le_into(vec);)+
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_be_into(vec);
                $(self.$idx.to_bits_be_into(vec);)+
            }
        }

        impl<'a, B: BooleanTrait, $t0: ToBitsInto<Boolean = B>, $($ty: ToBitsInto<Boolean = B>),+> ToBitsInto for &'a ($t0, $($ty),+) {
            type Boolean = B;

            /// A helper method to return a concatenated list of little-endian bits from the circuits.
            #[inline]
            fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
                // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
                self.$i0.to_bits_le_into(vec);
                $(self.$idx.to_bits_le_into(vec);)+
            }

            /// A helper method to return a concatenated list of big-endian bits from the circuits.
            #[inline]
            fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
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
