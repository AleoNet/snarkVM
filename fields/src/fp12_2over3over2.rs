// Copyright 2024 Aleo Network Foundation
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

use crate::{Field, Fp2, Fp2Parameters, One, Zero, fp6_3over2::*};
use snarkvm_utilities::{FromBytes, ToBits, ToBytes, bititerator::BitIteratorBE, rand::Uniform, serialize::*};

use rand::{
    Rng,
    distributions::{Distribution, Standard},
};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    fmt::Debug,
    hash::Hash,
    io::{Read, Result as IoResult, Write},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

pub trait Fp12Parameters: 'static + Copy + Clone + Debug + Default + PartialEq + Eq + Hash + Send + Sync {
    type Fp6Params: Fp6Parameters;

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP12_C1: [Fp2<Fp2Params<Self>>; 12];
}

type Fp2Params<P> = <<P as Fp12Parameters>::Fp6Params as Fp6Parameters>::Fp2Params;

/// An element of Fp12, represented by c0 + c1 * v
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Fp12<P: Fp12Parameters> {
    pub c0: Fp6<P::Fp6Params>,
    pub c1: Fp6<P::Fp6Params>,
}

impl<P: Fp12Parameters> Fp12<P> {
    /// Initializes an element of `Fp12` from two `Fp6` elements.
    pub const fn new(c0: Fp6<P::Fp6Params>, c1: Fp6<P::Fp6Params>) -> Self {
        Self { c0, c1 }
    }
}

impl<P: Fp12Parameters> Fp12<P> {
    pub fn conjugate(&mut self) {
        self.c1 = self.c1.neg();
    }

    pub fn mul_by_fp(&mut self, element: &<<P::Fp6Params as Fp6Parameters>::Fp2Params as Fp2Parameters>::Fp) {
        self.c0.mul_by_fp(element);
        self.c1.mul_by_fp(element);
    }

    /// Multiply by quadratic nonresidue v.
    #[inline(always)]
    pub(crate) fn mul_fp6_by_nonresidue(fe: &Fp6<P::Fp6Params>) -> Fp6<P::Fp6Params> {
        let new_c0 = P::Fp6Params::mul_fp2_by_nonresidue(&fe.c2);
        let new_c1 = fe.c0;
        let new_c2 = fe.c1;
        Fp6::new(new_c0, new_c1, new_c2)
    }

    pub fn mul_by_034(&mut self, c0: &Fp2<Fp2Params<P>>, c3: &Fp2<Fp2Params<P>>, c4: &Fp2<Fp2Params<P>>) {
        let a0 = self.c0.c0 * c0;
        let a1 = self.c0.c1 * c0;
        let a2 = self.c0.c2 * c0;
        let a = Fp6::new(a0, a1, a2);
        let mut b = self.c1;
        b.mul_by_01(c3, c4);

        let c0 = *c0 + c3;
        let c1 = c4;
        let mut e = self.c0 + self.c1;
        e.mul_by_01(&c0, c1);
        self.c1 = e - (a + b);
        self.c0 = a + Self::mul_fp6_by_nonresidue(&b);
    }

    pub fn mul_by_014(&mut self, c0: &Fp2<Fp2Params<P>>, c1: &Fp2<Fp2Params<P>>, c4: &Fp2<Fp2Params<P>>) {
        let mut aa = self.c0;
        aa.mul_by_01(c0, c1);
        let mut bb = self.c1;
        bb.mul_by_1(c4);
        let mut o = *c1;
        o.add_assign(c4);
        self.c1.add_assign(self.c0);
        self.c1.mul_by_01(c0, &o);
        self.c1.sub_assign(&aa);
        self.c1.sub_assign(&bb);
        self.c0 = bb;
        self.c0 = Self::mul_fp6_by_nonresidue(&self.c0);
        self.c0.add_assign(aa);
    }

    pub fn cyclotomic_square(&self) -> Self {
        let mut result = Self::zero();
        let fp2_nr = <P::Fp6Params as Fp6Parameters>::mul_fp2_by_nonresidue;

        let mut z0 = self.c0.c0;
        let mut z4 = self.c0.c1;
        let mut z3 = self.c0.c2;
        let mut z2 = self.c1.c0;
        let mut z1 = self.c1.c1;
        let mut z5 = self.c1.c2;

        // t0 + t1*y = (z0 + z1*y)^2 = a^2
        let mut tmp = z0 * z1;
        let t0 = (z0 + z1) * (z0 + fp2_nr(&z1)) - tmp - fp2_nr(&tmp);
        let t1 = tmp.double();

        // t2 + t3*y = (z2 + z3*y)^2 = b^2
        tmp = z2 * z3;
        let t2 = (z2 + z3) * (z2 + fp2_nr(&z3)) - tmp - fp2_nr(&tmp);
        let t3 = tmp.double();

        // t4 + t5*y = (z4 + z5*y)^2 = c^2
        tmp = z4 * z5;
        let t4 = (z4 + z5) * (z4 + fp2_nr(&z5)) - tmp - fp2_nr(&tmp);
        let t5 = tmp.double();

        // for A

        // z0 = 3 * t0 - 2 * z0
        z0 = t0 - z0;
        z0 = z0 + z0;
        result.c0.c0 = z0 + t0;

        // z1 = 3 * t1 + 2 * z1
        z1 = t1 + z1;
        z1 = z1 + z1;
        result.c1.c1 = z1 + t1;

        // for B

        // z2 = 3 * (xi * t5) + 2 * z2
        tmp = fp2_nr(&t5);
        z2 = tmp + z2;
        z2 = z2 + z2;
        result.c1.c0 = z2 + tmp;

        // z3 = 3 * t4 - 2 * z3
        z3 = t4 - z3;
        z3 = z3 + z3;
        result.c0.c2 = z3 + t4;

        // for C

        // z4 = 3 * t2 - 2 * z4
        z4 = t2 - z4;
        z4 = z4 + z4;
        result.c0.c1 = z4 + t2;

        // z5 = 3 * t3 + 2 * z5
        z5 = t3 + z5;
        z5 = z5 + z5;
        result.c1.c2 = z5 + t3;

        result
    }

    pub fn cyclotomic_exp<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        let mut res = Self::one();

        let mut found_one = false;

        for i in BitIteratorBE::new(exp) {
            if !found_one {
                if i {
                    found_one = true;
                } else {
                    continue;
                }
            }

            res = res.cyclotomic_square();

            if i {
                res *= self;
            }
        }
        res
    }
}

impl<P: Fp12Parameters> std::fmt::Display for Fp12<P> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "Fp12({} + {} * w)", self.c0, self.c1)
    }
}

impl<P: Fp12Parameters> Distribution<Fp12<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Fp12<P> {
        Fp12::new(Uniform::rand(rng), Uniform::rand(rng))
    }
}

impl<P: Fp12Parameters> Zero for Fp12<P> {
    fn zero() -> Self {
        Self::new(Fp6::zero(), Fp6::zero())
    }

    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }
}

impl<P: Fp12Parameters> One for Fp12<P> {
    fn one() -> Self {
        Self::new(Fp6::one(), Fp6::zero())
    }

    fn is_one(&self) -> bool {
        self.c0.is_one() && self.c1.is_zero()
    }
}

impl<P: Fp12Parameters> Field for Fp12<P> {
    type BasePrimeField = <Fp6<P::Fp6Params> as Field>::BasePrimeField;

    fn from_base_prime_field(other: Self::BasePrimeField) -> Self {
        Self::new(Fp6::from_base_prime_field(other), Fp6::zero())
    }

    #[inline]
    fn characteristic<'a>() -> &'a [u64] {
        Fp6::<P::Fp6Params>::characteristic()
    }

    fn double(&self) -> Self {
        let mut copy = *self;
        copy.double_in_place();
        copy
    }

    #[inline]
    fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
        let split_at = bytes.len() / 2;
        if let Some(c0) = Fp6::<P::Fp6Params>::from_random_bytes(&bytes[..split_at]) {
            if let Some((c1, flags)) = Fp6::<P::Fp6Params>::from_random_bytes_with_flags::<F>(&bytes[split_at..]) {
                return Some((Fp12::new(c0, c1), flags));
            }
        }
        None
    }

    #[inline]
    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::from_random_bytes_with_flags::<EmptyFlags>(bytes).map(|f| f.0)
    }

    fn double_in_place(&mut self) {
        self.c0.double_in_place();
        self.c1.double_in_place();
    }

    fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);

        self.c1.c0.mul_assign(&P::FROBENIUS_COEFF_FP12_C1[power % 12]);
        self.c1.c1.mul_assign(&P::FROBENIUS_COEFF_FP12_C1[power % 12]);
        self.c1.c2.mul_assign(&P::FROBENIUS_COEFF_FP12_C1[power % 12]);
    }

    fn square(&self) -> Self {
        let mut copy = *self;
        copy.square_in_place();
        copy
    }

    fn square_in_place(&mut self) -> &mut Self {
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut c0c1 = self.c0;
        c0c1.add_assign(self.c1);
        let mut c0 = self.c1;
        c0 = Self::mul_fp6_by_nonresidue(&c0);
        c0.add_assign(self.c0);
        c0.mul_assign(&c0c1);
        c0.sub_assign(&ab);
        self.c1 = ab;
        self.c1.add_assign(ab);
        ab = Self::mul_fp6_by_nonresidue(&ab);
        c0.sub_assign(&ab);
        self.c0 = c0;
        self
    }

    fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            let mut c0s = self.c0;
            c0s.square_in_place();
            let mut c1s = self.c1;
            c1s.square_in_place();
            c1s = Self::mul_fp6_by_nonresidue(&c1s);
            c0s.sub_assign(&c1s);

            c0s.inverse().map(|t| {
                let mut tmp = Fp12::new(t, t);
                tmp.c0.mul_assign(&self.c0);
                tmp.c1.mul_assign(&self.c1);
                tmp.c1 = -tmp.c1;

                tmp
            })
        }
    }

    fn inverse_in_place(&mut self) -> Option<&mut Self> {
        match self.inverse() {
            Some(inv) => {
                *self = inv;
                Some(self)
            }
            None => None,
        }
    }
}

impl<P: Fp12Parameters> Neg for Fp12<P> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        let mut copy = Self::zero();
        copy.c0 = self.c0.neg();
        copy.c1 = self.c1.neg();
        copy
    }
}

impl_add_sub_from_field_ref!(Fp12, Fp12Parameters);
impl_mul_div_from_field_ref!(Fp12, Fp12Parameters);

impl<'a, P: Fp12Parameters> Add<&'a Self> for Fp12<P> {
    type Output = Self;

    #[inline]
    fn add(self, other: &Self) -> Self {
        let mut result = self;
        result.add_assign(other);
        result
    }
}

impl<'a, P: Fp12Parameters> Sub<&'a Self> for Fp12<P> {
    type Output = Self;

    #[inline]
    fn sub(self, other: &Self) -> Self {
        let mut result = self;
        result.sub_assign(&other);
        result
    }
}

impl<'a, P: Fp12Parameters> Mul<&'a Self> for Fp12<P> {
    type Output = Self;

    #[inline]
    fn mul(self, other: &Self) -> Self {
        let mut result = self;
        result.mul_assign(&other);
        result
    }
}

impl<'a, P: Fp12Parameters> Div<&'a Self> for Fp12<P> {
    type Output = Self;

    #[inline]
    fn div(self, other: &Self) -> Self {
        let mut result = self;
        result.mul_assign(&other.inverse().unwrap());
        result
    }
}

impl<'a, P: Fp12Parameters> AddAssign<&'a Self> for Fp12<P> {
    #[inline]
    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(other.c0);
        self.c1.add_assign(other.c1);
    }
}

impl<'a, P: Fp12Parameters> SubAssign<&'a Self> for Fp12<P> {
    #[inline]
    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
    }
}

impl<'a, P: Fp12Parameters> MulAssign<&'a Self> for Fp12<P> {
    #[inline]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn mul_assign(&mut self, other: &Self) {
        let v0 = self.c0 * other.c0;
        let v1 = self.c1 * other.c1;
        self.c1 = (self.c0 + self.c1) * (other.c0 + other.c1) - v0 - v1;
        self.c0 = v0 + Self::mul_fp6_by_nonresidue(&v1);
    }
}

impl<'a, P: Fp12Parameters> DivAssign<&'a Self> for Fp12<P> {
    #[inline]
    fn div_assign(&mut self, other: &Self) {
        self.mul_assign(&other.inverse().unwrap());
    }
}

impl<P: Fp12Parameters> Ord for Fp12<P> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        let c1_cmp = self.c1.cmp(&other.c1);
        if c1_cmp == Ordering::Equal { self.c0.cmp(&other.c0) } else { c1_cmp }
    }
}

impl<P: Fp12Parameters> PartialOrd for Fp12<P> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: Fp12Parameters> From<u128> for Fp12<P> {
    fn from(other: u128) -> Self {
        Self::new(other.into(), Fp6::zero())
    }
}

impl<P: Fp12Parameters> From<u64> for Fp12<P> {
    fn from(other: u64) -> Self {
        Self::new(other.into(), Fp6::zero())
    }
}

impl<P: Fp12Parameters> From<u32> for Fp12<P> {
    fn from(other: u32) -> Self {
        Self::new(other.into(), Fp6::zero())
    }
}

impl<P: Fp12Parameters> From<u16> for Fp12<P> {
    fn from(other: u16) -> Self {
        Self::new(other.into(), Fp6::zero())
    }
}

impl<P: Fp12Parameters> From<u8> for Fp12<P> {
    fn from(other: u8) -> Self {
        Self::new(other.into(), Fp6::zero())
    }
}

impl<P: Fp12Parameters> ToBits for Fp12<P> {
    fn write_bits_le(&self, vec: &mut Vec<bool>) {
        self.c0.write_bits_le(vec);
        self.c1.write_bits_le(vec);
    }

    fn write_bits_be(&self, vec: &mut Vec<bool>) {
        self.c0.write_bits_be(vec);
        self.c1.write_bits_be(vec);
    }
}

impl<P: Fp12Parameters> ToBytes for Fp12<P> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.c0.write_le(&mut writer)?;
        self.c1.write_le(&mut writer)
    }
}

impl<P: Fp12Parameters> FromBytes for Fp12<P> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let c0 = Fp6::read_le(&mut reader)?;
        let c1 = Fp6::read_le(&mut reader)?;
        Ok(Fp12::new(c0, c1))
    }
}

impl<P: Fp12Parameters> CanonicalSerializeWithFlags for Fp12<P> {
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

impl<P: Fp12Parameters> CanonicalSerialize for Fp12<P> {
    #[inline]
    fn serialize_with_mode<W: Write>(&self, writer: W, _compress: Compress) -> Result<(), SerializationError> {
        self.serialize_with_flags(writer, EmptyFlags)
    }

    #[inline]
    fn serialized_size(&self, compress: Compress) -> usize {
        self.c0.serialized_size(compress) + self.c1.serialized_size(compress)
    }
}

impl<P: Fp12Parameters> CanonicalDeserializeWithFlags for Fp12<P> {
    #[inline]
    fn deserialize_with_flags<R: Read, F: Flags>(mut reader: R) -> Result<(Self, F), SerializationError> {
        let c0 = CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
        let (c1, flags) = Fp6::deserialize_with_flags(&mut reader)?;
        Ok((Self::new(c0, c1), flags))
    }
}

impl<P: Fp12Parameters> Valid for Fp12<P> {
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

impl<P: Fp12Parameters> CanonicalDeserialize for Fp12<P> {
    #[inline]
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let c0 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        let c1 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        Ok(Fp12::new(c0, c1))
    }
}
