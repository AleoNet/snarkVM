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

use crate::BooleanTrait;

/// Unary operator for converting to bits.
pub trait ToBits {
    type Boolean: BooleanTrait;

    /// Returns the little-endian bits of the circuit.
    fn to_bits_le(&self) -> Vec<Self::Boolean>;

    /// Returns the big-endian bits of the circuit.
    fn to_bits_be(&self) -> Vec<Self::Boolean>;
}

/********************/
/****** Arrays ******/
/********************/

impl<C: ToBits<Boolean = B>, B: BooleanTrait> ToBits for Vec<C> {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // The vector is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_le()
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // The vector is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_be()
    }
}

impl<C: ToBits<Boolean = B>, B: BooleanTrait, const N: usize> ToBits for [C; N] {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_le()
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.as_slice().to_bits_be()
    }
}

impl<C: ToBits<Boolean = B>, B: BooleanTrait> ToBits for &[C] {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.iter().flat_map(|c| c.to_bits_le()).collect()
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // The slice is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.iter().flat_map(|c| c.to_bits_be()).collect()
    }
}

/********************/
/****** Tuples ******/
/********************/

impl<'a, C0: ToBits<Boolean = B>, C1: ToBits<Boolean = B>, B: BooleanTrait> ToBits for (&'a C0, &'a C1) {
    type Boolean = B;

    /// A helper method to return a concatenated list of little-endian bits from the circuits.
    #[inline]
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.0.to_bits_le().into_iter().chain(self.1.to_bits_le().into_iter()).collect()
    }

    /// A helper method to return a concatenated list of big-endian bits from the circuits.
    #[inline]
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // The tuple is order-preserving, meaning the first circuit in is the first circuit bits out.
        self.0.to_bits_be().into_iter().chain(self.1.to_bits_be().into_iter()).collect()
    }
}
