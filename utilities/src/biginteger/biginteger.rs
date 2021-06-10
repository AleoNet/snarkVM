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

use crate::{
    bititerator::{BitIteratorBE, BitIteratorLE},
    bytes::{FromBytes, ToBytes},
    io::{Read, Result as IoResult, Write},
    rand::UniformRand,
};

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use std::fmt::{Debug, Display};

bigint_impl!(BigInteger64, 1);
bigint_impl!(BigInteger128, 2);
bigint_impl!(BigInteger256, 4);
bigint_impl!(BigInteger320, 5);
bigint_impl!(BigInteger384, 6);
bigint_impl!(BigInteger768, 12);
bigint_impl!(BigInteger832, 13);

/// TODO (howardwu): Update to use ToBitsLE and ToBitsBE.
/// This defines a `BigInteger`, a smart wrapper around a
/// sequence of `u64` limbs, least-significant digit first.
pub trait BigInteger:
    ToBytes
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
    + UniformRand
    + AsMut<[u64]>
    + AsRef<[u64]>
    + From<u64>
{
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

    /// Returns the big integer representation of a given big endian boolean
    /// array.
    fn from_bits_be(bits: Vec<bool>) -> Self;

    /// Returns the bit representation of the big integer in a big endian boolean array, without
    /// leading zeros.
    fn to_bits_be(&self) -> Vec<bool>;

    /// Returns the bit representation of the big integer in a little endian boolean array,
    /// with trailing zeroes.
    fn to_bits_le(&self) -> Vec<bool> {
        BitIteratorLE::new(self).collect::<Vec<_>>()
    }

    /// Returns a vector for wnaf.
    fn find_wnaf(&self) -> Vec<i64>;

    /// Writes this `BigInteger` as a big endian integer. Always writes
    /// `(num_bits` / 8) bytes.
    fn write_le<W: Write>(&self, writer: &mut W) -> IoResult<()> {
        self.write(writer)
    }

    /// Reads a big endian integer occupying (`num_bits` / 8) bytes into this
    /// representation.
    fn read_le<R: Read>(&mut self, reader: &mut R) -> IoResult<()> {
        *self = Self::read(reader)?;
        Ok(())
    }


    /// swaps endian of internal storage
    fn swap_endian(mut self) -> Self {
        let inner = self.as_mut();
        for x in inner {
            *x = x.swap_bytes();
        }
        self
    }
}

pub mod arithmetic {
    // #[cfg(all(target_arch = "x86_64", target_feature = "adx"))]
    // #[inline(always)]
    // pub fn adc_u8(a: u64, b: u64, carry: &mut u8) -> u64 {
    //     let mut out = 0u64;
    //     *carry = unsafe { core::arch::x86_64::_addcarryx_u64(*carry, a, b, &mut out) };
    //     out
    // }

    // #[cfg(all(target_arch = "x86_64", not(target_feature = "adx")))]
    // #[inline(always)]
    // pub fn adc_u8(a: u64, b: u64, carry: &mut u8) -> u64 {
    //     let mut out = 0u64;
    //     *carry = unsafe { core::arch::x86_64::_addcarry_u64(*carry, a, b, &mut out) };
    //     out
    // }

    // #[cfg(not(target_arch = "x86_64"))]
    pub fn adc_u8(a: u64, b: u64, carry: &mut u8) -> u64 {
        let tmp = u128::from(a) + u128::from(b) + u128::from(*carry);

        *carry = (tmp >> 64) as u8;

        tmp as u64
    }

    /// Calculate a + b + carry, returning the sum and modifying the
    /// carry value.
    #[inline(always)]
    pub fn adc(a: u64, b: u64, carry: &mut u64) -> u64 {
        let tmp = u128::from(a) + u128::from(b) + u128::from(*carry);

        *carry = (tmp >> 64) as u64;

        tmp as u64
    }

    // #[cfg(target_arch = "x86_64")]
    // #[inline(always)]
    // pub fn sbb(a: u64, b: u64, borrow: &mut u8) -> u64 {
    //     let mut out = 0u64;
    //     *borrow = unsafe { core::arch::x86_64::_subborrow_u64(*borrow, a, b, &mut out) };
    //     out
    // }

    // #[cfg(not(target_arch = "x86_64"))]
    pub fn sbb(a: u64, b: u64, borrow: &mut u8) -> u64 {
        let tmp = (1u128 << 64) + u128::from(a) - u128::from(b) - u128::from(*borrow);

        *borrow = if tmp >> 64 == 0 { 1 } else { 0 };

        tmp as u64
    }

    /// Calculate a + (b * c) + carry, returning the least significant digit
    /// and setting carry to the most significant digit.
    #[inline(always)]
    pub fn mac_with_carry(a: u64, b: u64, c: u64, carry: &mut u64) -> u64 {
        // let mut a_and_carry = 0u64;
        // let a_carry = unsafe { core::arch::x86_64::_addcarryx_u64(0, a, *carry, &mut a_and_carry) };

        // let mut hi = 0u64;
        // let mut lo = unsafe { core::arch::x86_64::_mulx_u64(b, c, &mut hi) };
        // let a_low_carry = unsafe { core::arch::x86_64::_addcarryx_u64(0, a_and_carry, lo, &mut lo) };

        // *carry = hi + a_low_carry as u64 + a_carry as u64;

        // lo
        let tmp = (u128::from(a)) + u128::from(b) * u128::from(c) + u128::from(*carry);

        *carry = (tmp >> 64) as u64;

        tmp as u64
    }
}

impl BigInteger256 {
    pub fn from_u128(num: u128) -> Self {
        // Takes a 256 bit buffer
        let mut bytes = [0u8; 32];

        num.write(bytes.as_mut()).unwrap();

        Self::read(&bytes[..]).unwrap()
    }

    pub fn to_u128(&self) -> u128 {
        let mut bytes = [0u8; 32];

        self.write(bytes.as_mut()).unwrap();

        // We cut off the last 128 bits here
        u128::read(&bytes[..16]).unwrap()
    }
}
