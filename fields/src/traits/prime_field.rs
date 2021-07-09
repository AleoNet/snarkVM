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

use crate::{FftField, FieldParameters};
use snarkvm_utilities::biginteger::BigInteger;

use std::str::FromStr;

/// The interface for a prime field.
#[allow(clippy::wrong_self_convention)]
pub trait PrimeField: FftField<FftParameters = <Self as PrimeField>::Parameters> + FromStr {
    type Parameters: FieldParameters<BigInteger = Self::BigInteger>;
    type BigInteger: BigInteger;

    /// Returns a prime field element from its underlying representation.
    fn from_repr(repr: Self::BigInteger) -> Option<Self>;

    /// Returns the underlying representation of the prime field element.
    fn into_repr(&self) -> Self::BigInteger;

    /// Returns a prime field element from its underlying raw representation.
    fn from_repr_unsafe(repr: Self::BigInteger) -> Self;

    /// Returns the underlying raw representation of the prime field element.
    fn into_repr_unsafe(&self) -> Self::BigInteger;

    /// Returns the field size in bits.
    fn size_in_bits() -> usize {
        Self::Parameters::MODULUS_BITS as usize
    }

    /// Returns the trace.
    fn trace() -> Self::BigInteger {
        Self::Parameters::T
    }

    /// Returns the trace minus one divided by two.
    fn trace_minus_one_div_two() -> Self::BigInteger {
        Self::Parameters::T_MINUS_ONE_DIV_TWO
    }

    /// Returns the modulus minus one divided by two.
    fn modulus_minus_one_div_two() -> Self::BigInteger {
        Self::Parameters::MODULUS_MINUS_ONE_DIV_TWO
    }
}
