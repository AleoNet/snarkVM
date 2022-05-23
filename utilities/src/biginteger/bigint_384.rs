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

use crate::{
    biginteger::BigInteger,
    bititerator::{BitIteratorBE, BitIteratorLE},
    io::{Read, Result as IoResult, Write},
    FromBits,
    FromBytes,
    ToBits,
    ToBytes,
};

use anyhow::Result;
use core::fmt::{Debug, Display};
use num_bigint::BigUint;
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};

#[derive(Copy, Clone, PartialEq, Eq, Default, Hash)]
pub struct BigInteger384(pub [u64; 6]);

impl BigInteger384 {
    pub const fn new(value: [u64; 6]) -> Self {
        BigInteger384(value)
    }
}
impl BigInteger for BigInteger384 {
    const NUM_LIMBS: usize = 6;

    #[inline]
    fn add_nocarry(&mut self, other: &Self) -> bool {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            use core::arch::x86_64::_addcarry_u64;
            let mut carry = 0;
            carry = _addcarry_u64(carry, self.0[0], other.0[0], &mut self.0[0]);
            carry = _addcarry_u64(carry, self.0[1], other.0[1], &mut self.0[1]);
            carry = _addcarry_u64(carry, self.0[2], other.0[2], &mut self.0[2]);
            carry = _addcarry_u64(carry, self.0[3], other.0[3], &mut self.0[3]);
            carry = _addcarry_u64(carry, self.0[4], other.0[4], &mut self.0[4]);
            carry = _addcarry_u64(carry, self.0[5], other.0[5], &mut self.0[5]);
            carry != 0
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            let mut carry = 0;
            carry = super::arithmetic::adc(&mut self.0[0], other.0[0], carry);
            carry = super::arithmetic::adc(&mut self.0[1], other.0[1], carry);
            carry = super::arithmetic::adc(&mut self.0[2], other.0[2], carry);
            carry = super::arithmetic::adc(&mut self.0[3], other.0[3], carry);
            carry = super::arithmetic::adc(&mut self.0[4], other.0[4], carry);
            carry = super::arithmetic::adc(&mut self.0[5], other.0[5], carry);
            carry != 0
        }
    }

    #[inline]
    fn sub_noborrow(&mut self, other: &Self) -> bool {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            use core::arch::x86_64::_subborrow_u64;
            let mut borrow = 0;
            borrow = _subborrow_u64(borrow, self.0[0], other.0[0], &mut self.0[0]);
            borrow = _subborrow_u64(borrow, self.0[1], other.0[1], &mut self.0[1]);
            borrow = _subborrow_u64(borrow, self.0[2], other.0[2], &mut self.0[2]);
            borrow = _subborrow_u64(borrow, self.0[3], other.0[3], &mut self.0[3]);
            borrow = _subborrow_u64(borrow, self.0[4], other.0[4], &mut self.0[4]);
            borrow = _subborrow_u64(borrow, self.0[5], other.0[5], &mut self.0[5]);
            borrow != 0
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            let mut borrow = 0;
            borrow = super::arithmetic::sbb(&mut self.0[0], other.0[0], borrow);
            borrow = super::arithmetic::sbb(&mut self.0[1], other.0[1], borrow);
            borrow = super::arithmetic::sbb(&mut self.0[2], other.0[2], borrow);
            borrow = super::arithmetic::sbb(&mut self.0[3], other.0[3], borrow);
            borrow = super::arithmetic::sbb(&mut self.0[4], other.0[4], borrow);
            borrow = super::arithmetic::sbb(&mut self.0[5], other.0[5], borrow);
            borrow != 0
        }
    }

    #[inline]
    fn mul2(&mut self) {
        let mut last = 0;
        for i in &mut self.0 {
            let tmp = *i >> 63;
            *i <<= 1;
            *i |= last;
            last = tmp;
        }
    }

    #[inline]
    fn muln(&mut self, mut n: u32) {
        if n >= 64 * 6 {
            *self = Self::from(0);
            return;
        }
        while n >= 64 {
            let mut t = 0;
            for i in &mut self.0 {
                std::mem::swap(&mut t, i);
            }
            n -= 64;
        }
        if n > 0 {
            let mut t = 0;
            for i in &mut self.0 {
                let t2 = *i >> (64 - n);
                *i <<= n;
                *i |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn div2(&mut self) {
        let mut t = 0;
        for i in self.0.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    }

    #[inline]
    fn divn(&mut self, mut n: u32) {
        if n >= 64 * 6 {
            *self = Self::from(0);
            return;
        }
        while n >= 64 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                std::mem::swap(&mut t, i);
            }
            n -= 64;
        }
        if n > 0 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                let t2 = *i << (64 - n);
                *i >>= n;
                *i |= t;
                t = t2;
            }
        }
    }

    #[inline]
    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    #[inline]
    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.iter().all(|&e| e == 0)
    }

    #[inline]
    fn num_bits(&self) -> u32 {
        let mut ret = 6 * 64;
        for i in self.0.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != 64 {
                break;
            }
        }
        ret
    }

    #[inline]
    fn get_bit(&self, i: usize) -> bool {
        if i >= 64 * 6 {
            false
        } else {
            let limb = i / 64;
            let bit = i - (64 * limb);
            (self.0[limb] & (1 << bit)) != 0
        }
    }

    #[inline]
    fn to_biguint(&self) -> num_bigint::BigUint {
        BigUint::from_bytes_le(&self.to_bytes_le().unwrap())
    }

    #[inline]
    fn find_wnaf(&self) -> Vec<i64> {
        let mut res = crate::vec::Vec::new();
        let mut e = *self;
        while !e.is_zero() {
            let z: i64;
            if e.is_odd() {
                z = 2 - (e.0[0] % 4) as i64;
                if z >= 0 {
                    e.sub_noborrow(&Self::from(z as u64));
                } else {
                    e.add_nocarry(&Self::from((-z) as u64));
                }
            } else {
                z = 0;
            }
            res.push(z);
            e.div2();
        }
        res
    }
}
impl ToBits for BigInteger384 {
    #[doc = " Returns `self` as a boolean array in little-endian order, with trailing zeros."]
    fn to_bits_le(&self) -> Vec<bool> {
        BitIteratorLE::new(self).collect::<Vec<_>>()
    }

    #[doc = " Returns `self` as a boolean array in big-endian order, with leading zeros."]
    fn to_bits_be(&self) -> Vec<bool> {
        BitIteratorBE::new(self).collect::<Vec<_>>()
    }
}
impl FromBits for BigInteger384 {
    #[doc = " Returns a `BigInteger` by parsing a slice of bits in little-endian format"]
    #[doc = " and transforms it into a slice of little-endian u64 elements."]
    fn from_bits_le(bits: &[bool]) -> Result<Self> {
        let mut res = Self::default();
        for (i, bits64) in bits.chunks(64).enumerate() {
            let mut acc: u64 = 0;
            for bit in bits64.iter().rev() {
                acc <<= 1;
                acc += *bit as u64;
            }
            res.0[i] = acc;
        }
        Ok(res)
    }

    #[doc = " Returns a `BigInteger` by parsing a slice of bits in big-endian format"]
    #[doc = " and transforms it into a slice of little-endian u64 elements."]
    fn from_bits_be(bits: &[bool]) -> Result<Self> {
        let mut bits_reversed = bits.to_vec();
        bits_reversed.reverse();
        Self::from_bits_le(&bits_reversed)
    }
}
impl ToBytes for BigInteger384 {
    #[inline]
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        self.0.write_le(writer)
    }
}
impl FromBytes for BigInteger384 {
    #[inline]
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        <[u64; 6]>::read_le(reader).map(Self::new)
    }
}
impl Debug for BigInteger384 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in self.0.iter().rev() {
            write!(f, "{:016X}", *i)?;
        }
        Ok(())
    }
}
impl Display for BigInteger384 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_biguint())
    }
}
impl Ord for BigInteger384 {
    #[inline]
    #[allow(clippy::comparison_chain)]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
            if a < b {
                return std::cmp::Ordering::Less;
            } else if a > b {
                return std::cmp::Ordering::Greater;
            }
        }
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for BigInteger384 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Distribution<BigInteger384> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> BigInteger384 {
        BigInteger384(rng.gen())
    }
}
impl AsMut<[u64]> for BigInteger384 {
    #[inline]
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }
}
impl AsRef<[u64]> for BigInteger384 {
    #[inline]
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}
impl From<u64> for BigInteger384 {
    #[inline]
    fn from(val: u64) -> BigInteger384 {
        let mut repr = Self::default();
        repr.0[0] = val;
        repr
    }
}
