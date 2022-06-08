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

use crate::{rand::Uniform, FromBits, FromBytes, ToBits, ToBytes};

use num_bigint::BigUint;
use std::fmt::{Debug, Display};

mod bigint_256;
pub use bigint_256::*;

mod bigint_384;
pub use bigint_384::*;

#[cfg(test)]
mod tests;

/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant digit first.
pub trait BigInteger:
    ToBits
    + FromBits
    + ToBytes
    + FromBytes
    + Copy
    + Clone
    + Debug
    + Default
    + Display
    + Eq
    + Ord
    + Send
    + Sized
    + Sync
    + 'static
    + Uniform
    + AsMut<[u64]>
    + AsRef<[u64]>
    + From<u64>
{
    /// The number of limbs used in this BigInteger.
    const NUM_LIMBS: usize;

    /// Add another representation to this one, returning the carry bit.
    fn add_nocarry(&mut self, other: &Self) -> bool;

    /// Subtract another representation from this one, returning the borrow bit.
    fn sub_noborrow(&mut self, other: &Self) -> bool;

    /// Performs a leftwise bitshift of this number, effectively multiplying
    /// it by 2. Overflow is ignored.
    fn mul2(&mut self);

    /// Performs a leftwise bitshift of this number by some amount.
    fn muln(&mut self, amt: u32);

    /// Performs a rightwise bitshift of this number, effectively dividing
    /// it by 2.
    fn div2(&mut self);

    /// Performs a rightwise bitshift of this number by some amount.
    fn divn(&mut self, amt: u32);

    /// Returns true iff this number is odd.
    fn is_odd(&self) -> bool;

    /// Returns true iff this number is even.
    fn is_even(&self) -> bool;

    /// Returns true iff this number is zero.
    fn is_zero(&self) -> bool;

    /// Compute the number of bits needed to encode this number. Always a
    /// multiple of 64.
    fn num_bits(&self) -> u32;

    /// Compute the `i`-th bit of `self`.
    fn get_bit(&self, i: usize) -> bool;

    /// Returns the BigUint representation.
    fn to_biguint(&self) -> BigUint;

    /// Returns a vector for wnaf.
    fn find_wnaf(&self) -> Vec<i64>;
}

pub mod arithmetic {
    /// Calculate a + b + carry, returning the sum and modifying the
    /// carry value.
    #[inline(always)]
    pub fn adc(a: &mut u64, b: u64, carry: u64) -> u64 {
        let tmp = u128::from(*a) + u128::from(b) + u128::from(carry);
        *a = tmp as u64;
        (tmp >> 64) as u64
    }

    /// set a = a - b - borrow, and returning the borrow value.
    #[inline(always)]
    pub fn sbb(a: &mut u64, b: u64, borrow: u64) -> u64 {
        let tmp = (1u128 << 64) + u128::from(*a) - u128::from(b) - u128::from(borrow);
        let carry = if tmp >> 64 == 0 { 1 } else { 0 };
        *a = tmp as u64;
        carry
    }

    /// Calculate a + (b * c) + carry, returning the least significant digit
    /// and setting carry to the most significant digit.
    #[inline(always)]
    pub fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
        let tmp = (u128::from(a)) + u128::from(b) * u128::from(c) + u128::from(*carry);

        *carry = (tmp >> 64) as u64;

        tmp as u64
    }

    /// Calculate a + b * c, returning the lower 64 bits of the result and setting
    /// `carry` to the upper 64 bits.
    #[inline(always)]
    pub fn mac(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
        let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

        *carry = (tmp >> 64) as u64;

        tmp as u64
    }

    /// Calculate a + b * c, discarding the lower 64 bits of the result and setting
    /// `carry` to the upper 64 bits.
    #[inline(always)]
    pub fn mac_discard(a: u64, b: u64, c: u64, carry: &mut u64) {
        let tmp = (u128::from(a)) + u128::from(b) * u128::from(c);

        *carry = (tmp >> 64) as u64;
    }
}
