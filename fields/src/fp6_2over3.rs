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

use crate::{Field, Fp3, Fp3Parameters, One, Zero};
use snarkvm_utilities::{
    biginteger::BigInteger,
    errors::SerializationError,
    rand::UniformRand,
    serialize::*,
    FromBytes,
    ToBits,
    ToBytes,
};

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    io::{Read, Result as IoResult, Write},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub trait Fp6Parameters: 'static + Send + Sync {
    type Fp3Params: Fp3Parameters;

    const NONRESIDUE: Fp3<Self::Fp3Params>;

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP6_C1: [<Self::Fp3Params as Fp3Parameters>::Fp; 6];

    #[inline(always)]
    fn mul_fp3_by_nonresidue(fe: &Fp3<Self::Fp3Params>) -> Fp3<Self::Fp3Params> {
        Self::NONRESIDUE * fe
    }
}

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Default(bound = "P: Fp6Parameters"),
    Hash(bound = "P: Fp6Parameters"),
    Clone(bound = "P: Fp6Parameters"),
    Copy(bound = "P: Fp6Parameters"),
    Debug(bound = "P: Fp6Parameters"),
    PartialEq(bound = "P: Fp6Parameters"),
    Eq(bound = "P: Fp6Parameters")
)]
pub struct Fp6<P: Fp6Parameters> {
    pub c0: Fp3<P::Fp3Params>,
    pub c1: Fp3<P::Fp3Params>,
}

impl<P: Fp6Parameters> Fp6<P> {
    pub fn new(c0: Fp3<P::Fp3Params>, c1: Fp3<P::Fp3Params>) -> Self {
        Fp6 { c0, c1 }
    }

    pub fn conjugate(&mut self) {
        self.c1 = self.c1.neg();
    }

    pub fn mul_by_034(
        &mut self,
        c0: &<P::Fp3Params as Fp3Parameters>::Fp,
        c3: &<P::Fp3Params as Fp3Parameters>::Fp,
        c4: &<P::Fp3Params as Fp3Parameters>::Fp,
    ) {
        let z0 = self.c0.c0;
        let z1 = self.c0.c1;
        let z2 = self.c0.c2;
        let z3 = self.c1.c0;
        let z4 = self.c1.c1;
        let z5 = self.c1.c2;

        let x0 = *c0;
        let x3 = *c3;
        let x4 = *c4;

        let mut tmp1 = x3;
        tmp1.mul_assign(&<P::Fp3Params as Fp3Parameters>::NONRESIDUE);
        let mut tmp2 = x4;
        tmp2.mul_assign(&<P::Fp3Params as Fp3Parameters>::NONRESIDUE);

        self.c0.c0 = x0 * z0 + (tmp1 * z5) + (tmp2 * z4);
        self.c0.c1 = x0 * z1 + (x3 * z3) + (tmp2 * z5);
        self.c0.c2 = x0 * z2 + (x3 * z4) + (x4 * z3);
        self.c1.c0 = x0 * z3 + (x3 * z0) + (tmp2 * z2);
        self.c1.c1 = x0 * z4 + (x3 * z1) + (x4 * z0);
        self.c1.c2 = x0 * z5 + (x3 * z2) + (x4 * z1);
    }

    pub fn mul_by_014(
        &mut self,
        c0: &<P::Fp3Params as Fp3Parameters>::Fp,
        c1: &<P::Fp3Params as Fp3Parameters>::Fp,
        c4: &<P::Fp3Params as Fp3Parameters>::Fp,
    ) {
        let z0 = self.c0.c0;
        let z1 = self.c0.c1;
        let z2 = self.c0.c2;
        let z3 = self.c1.c0;
        let z4 = self.c1.c1;
        let z5 = self.c1.c2;

        let x0 = *c0;
        let x1 = *c1;
        let x4 = *c4;

        let mut tmp1 = x1;
        tmp1.mul_assign(&<P::Fp3Params as Fp3Parameters>::NONRESIDUE);
        let mut tmp2 = x4;
        tmp2.mul_assign(&<P::Fp3Params as Fp3Parameters>::NONRESIDUE);

        self.c0.c0 = x0 * z0 + (tmp1 * z2) + (tmp2 * z4);
        self.c0.c1 = x0 * z1 + (x1 * z0) + (tmp2 * z5);
        self.c0.c2 = x0 * z2 + (x1 * z1) + (x4 * z3);
        self.c1.c0 = x0 * z3 + (tmp1 * z5) + (tmp2 * z2);
        self.c1.c1 = x0 * z4 + (x1 * z3) + (x4 * z0);
        self.c1.c2 = x0 * z5 + (x1 * z4) + (x4 * z1);
    }

    /// Multiply by quadratic nonresidue v.
    pub fn mul_by_nonresidue(value: &Fp3<P::Fp3Params>) -> Fp3<P::Fp3Params> {
        let mut res = *value;
        res.c0 = value.c2;
        res.c1 = value.c0;
        res.c2 = value.c1;
        res.c0.mul_assign(&<P::Fp3Params as Fp3Parameters>::NONRESIDUE);
        res
    }

    pub fn unitary_inverse(&self) -> Self {
        Self::new(self.c0, -self.c1)
    }

    pub fn cyclotomic_exp<B: BigInteger>(&self, exponent: &B) -> Self {
        let mut res = Self::one();
        let self_inverse = self.unitary_inverse();

        let mut found_nonzero = false;
        let naf = exponent.find_wnaf();

        for &value in naf.iter().rev() {
            if found_nonzero {
                res = res.square();
            }

            if value != 0 {
                found_nonzero = true;

                if value > 0 {
                    res *= self;
                } else {
                    res *= &self_inverse;
                }
            }
        }

        res
    }
}

impl<P: Fp6Parameters> Zero for Fp6<P> {
    fn zero() -> Self {
        Fp6 {
            c0: Fp3::zero(),
            c1: Fp3::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
}

impl<P: Fp6Parameters> One for Fp6<P> {
    fn one() -> Self {
        Fp6 {
            c0: Fp3::one(),
            c1: Fp3::zero(),
        }
    }

    fn is_one(&self) -> bool {
        self.c0.is_one() && self.c1.is_zero()
    }
}

impl<P: Fp6Parameters> Field for Fp6<P> {
    #[inline]
    fn characteristic<'a>() -> &'a [u64] {
        Fp3::<P::Fp3Params>::characteristic()
    }

    fn double(&self) -> Self {
        let mut result = *self;
        result.double_in_place();
        result
    }

    fn double_in_place(&mut self) {
        self.c0.double_in_place();
        self.c1.double_in_place();
    }

    fn square(&self) -> Self {
        let mut result = *self;
        result.square_in_place();
        result
    }

    #[inline]
    fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        let split_at = bytes.len() / 2;
        if let Some(c0) = Fp3::<P::Fp3Params>::from_random_bytes(&bytes[..split_at]) {
            if let Some((c1, flags)) = Fp3::<P::Fp3Params>::from_random_bytes_with_flags::<F>(&bytes[split_at..]) {
                return Some((Fp6::new(c0, c1), flags));
            }
        }
        None
    }

    #[inline]
    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::from_random_bytes_with_flags::<EmptyFlags>(bytes).map(|f| f.0)
    }

    fn square_in_place(&mut self) -> &mut Self {
        // Devegili OhEig Scott Dahab --- Multiplication and Squaring on
        // Pairing-Friendly
        // Fields.pdf; Section 3 (Complex)
        let a = self.c0;
        let b = self.c1;
        let ab_add = a + b;
        let ab_mul = a * b;

        let c0 = ab_add * (a + Self::mul_by_nonresidue(&b)) - ab_mul - Self::mul_by_nonresidue(&ab_mul);
        let c1 = ab_mul.double();

        self.c0 = c0;
        self.c1 = c1;
        self
    }

    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            // From "High-Speed Software Implementation of the Optimal Ate Pairing over
            // Barreto-Naehrig
            // Curves"; Algorithm 8
            let a = self.c0;
            let b = self.c1;

            let t1 = b.square();
            let t0 = a.square() - Self::mul_by_nonresidue(&t1);
            let t2 = t0.inverse().unwrap();

            let c0 = a * t2;
            let c1 = (b * t2).neg();

            Some(Self::new(c0, c1))
        }
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        if let Some(inverse) = self.inverse() {
            *self = inverse;
            Some(self)
        } else {
            None
        }
    }

    fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);
        self.c1.mul_assign_by_fp(&P::FROBENIUS_COEFF_FP6_C1[power % 6]);
    }
}

/// `Fp6` elements are ordered lexicographically.
impl<P: Fp6Parameters> Ord for Fp6<P> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        let c1_cmp = self.c1.cmp(&other.c1);
        if c1_cmp == Ordering::Equal {
            self.c0.cmp(&other.c0)
        } else {
            c1_cmp
        }
    }
}

impl<P: Fp6Parameters> PartialOrd for Fp6<P> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: Fp6Parameters> From<u128> for Fp6<P> {
    fn from(other: u128) -> Self {
        Self::new(other.into(), Fp3::zero())
    }
}

impl<P: Fp6Parameters> From<u64> for Fp6<P> {
    fn from(other: u64) -> Self {
        Self::new(other.into(), Fp3::zero())
    }
}

impl<P: Fp6Parameters> From<u32> for Fp6<P> {
    fn from(other: u32) -> Self {
        Self::new(other.into(), Fp3::zero())
    }
}

impl<P: Fp6Parameters> From<u16> for Fp6<P> {
    fn from(other: u16) -> Self {
        Self::new(other.into(), Fp3::zero())
    }
}

impl<P: Fp6Parameters> From<u8> for Fp6<P> {
    fn from(other: u8) -> Self {
        Self::new(other.into(), Fp3::zero())
    }
}

impl<P: Fp6Parameters> ToBits for Fp6<P> {
    fn to_bits_le(&self) -> Vec<bool> {
        let mut res = vec![];
        res.extend_from_slice(&self.c0.to_bits_le());
        res.extend_from_slice(&self.c1.to_bits_le());
        res
    }

    fn to_bits_be(&self) -> Vec<bool> {
        let mut res = vec![];
        res.extend_from_slice(&self.c0.to_bits_be());
        res.extend_from_slice(&self.c1.to_bits_be());
        res
    }
}

impl<P: Fp6Parameters> ToBytes for Fp6<P> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.c0.write_le(&mut writer)?;
        self.c1.write_le(&mut writer)
    }
}

impl<P: Fp6Parameters> FromBytes for Fp6<P> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let c0 = Fp3::read_le(&mut reader)?;
        let c1 = Fp3::read_le(&mut reader)?;
        Ok(Fp6::new(c0, c1))
    }
}

impl<P: Fp6Parameters> Neg for Fp6<P> {
    type Output = Self;

    #[inline]
    fn neg(mut self) -> Self {
        self.c0 = self.c0.neg();
        self.c1 = self.c1.neg();
        self
    }
}

impl<P: Fp6Parameters> Distribution<Fp6<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Fp6<P> {
        Fp6::new(UniformRand::rand(rng), UniformRand::rand(rng))
    }
}

impl_add_sub_from_field_ref!(Fp6, Fp6Parameters);
impl_mul_div_from_field_ref!(Fp6, Fp6Parameters);

impl<'a, P: Fp6Parameters> Add<&'a Fp6<P>> for Fp6<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: &Self) -> Self {
        let mut result = self;
        result.add_assign(other);
        result
    }
}

impl<'a, P: Fp6Parameters> Sub<&'a Fp6<P>> for Fp6<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &Self) -> Self {
        let mut result = self;
        result.sub_assign(&other);
        result
    }
}

impl<'a, P: Fp6Parameters> Mul<&'a Fp6<P>> for Fp6<P> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &Self) -> Self {
        let mut result = self;
        result.mul_assign(&other);
        result
    }
}

impl<'a, P: Fp6Parameters> Div<&'a Fp6<P>> for Fp6<P> {
    type Output = Self;

    #[inline]
    fn div(self, other: &Self) -> Self {
        let mut result = self;
        result.mul_assign(&other.inverse().unwrap());
        result
    }
}

impl<'a, P: Fp6Parameters> AddAssign<&'a Self> for Fp6<P> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(other.c0);
        self.c1.add_assign(other.c1);
    }
}

impl<'a, P: Fp6Parameters> SubAssign<&'a Self> for Fp6<P> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
    }
}

impl<'a, P: Fp6Parameters> MulAssign<&'a Self> for Fp6<P> {
    #[inline]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn mul_assign(&mut self, other: &Self) {
        // Devegili OhEig Scott Dahab --- Multiplication and Squaring on
        // Pairing-Friendly
        // Fields.pdf; Section 3 (Karatsuba)
        let a0 = self.c0;
        let b0 = self.c1;
        let a1 = other.c0;
        let b1 = other.c1;

        let a0a1 = a0 * a1;
        let b0b1 = b0 * b1;
        let beta_b0b1 = Self::mul_by_nonresidue(&b0b1);

        let c0 = a0a1 + beta_b0b1;
        let c1 = (a0 + b0) * (a1 + b1) - a0a1 - b0b1;

        self.c0 = c0;
        self.c1 = c1;
    }
}

impl<'a, P: Fp6Parameters> DivAssign<&'a Self> for Fp6<P> {
    #[inline]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl<'a, P: Fp6Parameters> From<&'a [bool]> for Fp6<P> {
    fn from(_bits: &[bool]) -> Self {
        unimplemented!()
    }
}

impl<P: Fp6Parameters> ::std::fmt::Display for Fp6<P> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "Fp6_2over3({}, {})", self.c0, self.c1)
    }
}

impl<P: Fp6Parameters> CanonicalSerializeWithFlags for Fp6<P> {
    #[inline]
    fn serialize_with_flags<W: Write, F: Flags>(&self, mut writer: W, flags: F) -> Result<(), SerializationError> {
        self.c0.serialize_uncompressed(&mut writer)?;
        self.c1.serialize_with_flags(&mut writer, flags)?;
        Ok(())
    }

    fn serialized_size_with_flags<F: Flags>(&self) -> usize {
        self.c0.uncompressed_size() + self.c1.serialized_size_with_flags::<F>()
    }
}

impl<P: Fp6Parameters> CanonicalSerialize for Fp6<P> {
    #[inline]
    fn serialize_with_mode<W: Write>(&self, writer: W, _compress: Compress) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.c0.serialized_size(compress) + self.c1.serialized_size(compress)
    }
}

impl<P: Fp6Parameters> CanonicalDeserializeWithFlags for Fp6<P> {
    #[inline]
    fn deserialize_with_flags<R: Read, F: Flags>(mut reader: R) -> Result<(Self, F), SerializationError> {
        let c0 = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let (c1, flags) = Fp3::deserialize_with_flags(&mut reader)?;
        Ok((Fp6::new(c0, c1), flags))
    }
}

impl<P: Fp6Parameters> Valid for Fp6<P> {
    fn check(&self) -> Result<(), snarkvm_utilities::SerializationError> {
        Ok(())
    }

    fn batch_check<'a>(_batch: impl Iterator<Item = &'a Self>) -> Result<(), snarkvm_utilities::SerializationError>
    where
        Self: 'a,
    {
        Ok(())
    }
}

impl<P: Fp6Parameters> CanonicalDeserialize for Fp6<P> {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let c0 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let c1 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Fp6::new(c0, c1))
    }
}
