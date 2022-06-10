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

pub trait ToBits: Sized {
    /// Returns `self` as a boolean array in little-endian order.
    fn to_bits_le(&self) -> Vec<bool>;

    /// Returns `self` as a boolean array in big-endian order.
    fn to_bits_be(&self) -> Vec<bool>;
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
