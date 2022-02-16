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
    impl_edwards_curve_serializer,
    prefetch_slice,
    templates::twisted_edwards_extended::Projective,
    traits::{AffineCurve, Group, MontgomeryParameters, ProjectiveCurve, TwistedEdwardsParameters as Parameters},
};
use snarkvm_fields::{impl_add_sub_from_field_ref, Field, One, PrimeField, SquareRootField, Zero};
use snarkvm_utilities::{
    bititerator::BitIteratorBE,
    rand::UniformRand,
    serialize::*,
    FromBytes,
    ToBits,
    ToBytes,
    ToMinimalBits,
};

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{Deserialize, Serialize};
use std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

macro_rules! batch_add_loop_1 {
    ($a: ident, $b: ident, $inversion_tmp: ident) => {
        if $a.is_zero() || $b.is_zero() {
            continue;
        } else {
            let y1y2 = $a.y * &$b.y;
            let x1x2 = $a.x * &$b.x;

            $a.x = ($a.x + &$a.y) * &($b.x + &$b.y) - &y1y2 - &x1x2;
            $a.y = y1y2;
            if !P::COEFF_A.is_zero() {
                $a.y -= &P::mul_by_a(&x1x2);
            }

            let dx1x2y1y2 = P::COEFF_D * &y1y2 * &x1x2;

            let inversion_mul_d = $inversion_tmp * &dx1x2y1y2;

            $a.x *= &($inversion_tmp - &inversion_mul_d);
            $a.y *= &($inversion_tmp + &inversion_mul_d);

            $b.x = P::BaseField::one() - &dx1x2y1y2.square();

            $inversion_tmp *= &$b.x;
        }
    };
}

macro_rules! batch_add_loop_2 {
    ($a: ident, $b: ident, $inversion_tmp: ident) => {
        if $a.is_zero() {
            *$a = $b;
        } else if !$b.is_zero() {
            $a.x *= &$inversion_tmp;
            $a.y *= &$inversion_tmp;

            $inversion_tmp *= &$b.x;
        }
    };
}

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: MontgomeryParameters"),
    Clone(bound = "P: MontgomeryParameters"),
    PartialEq(bound = "P: MontgomeryParameters"),
    Eq(bound = "P: MontgomeryParameters"),
    Debug(bound = "P: MontgomeryParameters"),
    Hash(bound = "P: MontgomeryParameters")
)]
pub struct MontgomeryAffine<P: MontgomeryParameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
}

impl<P: MontgomeryParameters> MontgomeryAffine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
    }
}

impl<P: MontgomeryParameters> Display for MontgomeryAffine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "MontgomeryAffine(x={}, y={})", self.x, self.y)
    }
}

#[derive(Derivative, Serialize, Deserialize)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    PartialEq(bound = "P: Parameters"),
    Eq(bound = "P: Parameters"),
    Debug(bound = "P: Parameters"),
    Hash(bound = "P: Parameters")
)]
pub struct Affine<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
}

impl<P: Parameters> Affine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
    }

    #[must_use]
    pub fn scale_by_cofactor(&self) -> <Self as AffineCurve>::Projective {
        self.mul_bits(BitIteratorBE::new(P::COFACTOR))
    }
}

impl<P: Parameters> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        other.eq(self)
    }
}

impl<P: Parameters> Zero for Affine<P> {
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one())
    }

    fn is_zero(&self) -> bool {
        self.x.is_zero() & self.y.is_one()
    }
}

impl<P: Parameters> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Affine(x={}, y={})", self.x, self.y)
    }
}

impl<P: Parameters> AffineCurve for Affine<P> {
    type BaseField = P::BaseField;
    type Projective = Projective<P>;

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Self::new(P::AFFINE_GENERATOR_COEFFS.0, P::AFFINE_GENERATOR_COEFFS.1)
    }

    #[inline]
    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::BaseField::from_random_bytes_with_flags::<EdwardsFlags>(bytes).and_then(|(x, flags)| {
            // If x is valid and is zero, then parse this point as infinity.
            if x.is_zero() { Some(Self::zero()) } else { Self::from_x_coordinate(x, flags.is_positive()) }
        })
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    #[inline]
    fn from_x_coordinate(x: Self::BaseField, greatest: bool) -> Option<Self> {
        // y = sqrt( (a * x^2 - 1)  / (d * x^2 - 1) )
        let x2 = x.square();
        let one = Self::BaseField::one();
        let numerator = P::mul_by_a(&x2) - one;
        let denominator = P::COEFF_D * x2 - one;
        let y2 = denominator.inverse().map(|denom| denom * numerator);
        y2.and_then(|y2| y2.sqrt()).map(|y| {
            let negy = -y;
            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new(x, y)
        })
    }

    /// Attempts to construct an affine point given a y-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    #[inline]
    fn from_y_coordinate(y: Self::BaseField, greatest: bool) -> Option<Self> {
        // x = sqrt( (1 - y^2) / (a - d * y^2) )
        let y2 = y.square();
        let one = Self::BaseField::one();
        let numerator = one - y2;
        let denominator = P::mul_by_a(&one) - (P::COEFF_D * y2);
        let x2 = denominator.inverse().map(|denom| denom * numerator);
        x2.and_then(|x2| x2.sqrt()).map(|x| {
            let negx = -x;
            let x = if (x < negx) ^ greatest { x } else { negx };
            Self::new(x, y)
        })
    }

    fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> Projective<P> {
        let mut res = Projective::zero();
        for i in bits {
            res.double_in_place();
            if i {
                res.add_assign_mixed(self)
            }
        }
        res
    }

    fn mul_by_cofactor_to_projective(&self) -> Self::Projective {
        self.scale_by_cofactor()
    }

    fn mul_by_cofactor_inv(&self) -> Self {
        self.mul(P::COFACTOR_INV)
    }

    fn into_projective(&self) -> Projective<P> {
        (*self).into()
    }

    fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
        self.mul_bits(BitIteratorBE::new(P::ScalarField::characteristic())).is_zero()
    }

    fn to_x_coordinate(&self) -> Self::BaseField {
        self.x
    }

    fn to_y_coordinate(&self) -> Self::BaseField {
        self.y
    }

    /// Checks that the current point is on the elliptic curve.
    fn is_on_curve(&self) -> bool {
        let x2 = self.x.square();
        let y2 = self.y.square();

        let lhs = y2 + P::mul_by_a(&x2);
        let rhs = P::BaseField::one() + (P::COEFF_D * (x2 * y2));

        lhs == rhs
    }

    // Total cost: 12 mul. Projective formulas: 11 mul.
    fn batch_add_in_place_same_slice(bases: &mut [Self], index: &[(u32, u32)]) {
        let mut inversion_tmp = P::BaseField::one();

        #[cfg(target_arch = "x86_64")]
        let mut prefetch_iter = index.iter();
        #[cfg(target_arch = "x86_64")]
        {
            prefetch_iter.next();
        }

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            #[cfg(target_arch = "x86_64")]
            prefetch_slice!(bases, bases, prefetch_iter);
            let (mut a, mut b) = if idx < idy {
                let (x, y) = bases.split_at_mut(*idy as usize);
                (&mut x[*idx as usize], &mut y[0])
            } else {
                let (x, y) = bases.split_at_mut(*idx as usize);
                (&mut y[0], &mut x[*idy as usize])
            };
            batch_add_loop_1!(a, b, inversion_tmp);
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        #[cfg(target_arch = "x86_64")]
        let mut prefetch_iter = index.iter().rev();
        #[cfg(target_arch = "x86_64")]
        {
            prefetch_iter.next();
        }

        for (idx, idy) in index.iter().rev() {
            #[cfg(target_arch = "x86_64")]
            prefetch_slice!(bases, bases, prefetch_iter);
            let (mut a, b) = if idx < idy {
                let (x, y) = bases.split_at_mut(*idy as usize);
                (&mut x[*idx as usize], y[0])
            } else {
                let (x, y) = bases.split_at_mut(*idx as usize);
                (&mut y[0], x[*idy as usize])
            };
            batch_add_loop_2!(a, b, inversion_tmp);
        }
    }
}

impl<P: Parameters> ToMinimalBits for Affine<P> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        self.x.to_bits_le()
    }
}

impl<P: Parameters> Group for Affine<P> {
    type ScalarField = P::ScalarField;

    #[inline]
    #[must_use]
    fn double(&self) -> Self {
        let mut tmp = *self;
        tmp += self;
        tmp
    }

    #[inline]
    fn double_in_place(&mut self) {
        let tmp = *self;
        *self = tmp.double();
    }
}

impl<P: Parameters> Neg for Affine<P> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.x, self.y)
    }
}

impl_add_sub_from_field_ref!(Affine, Parameters);

impl<'a, P: Parameters> Add<&'a Self> for Affine<P> {
    type Output = Self;

    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for Affine<P> {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn add_assign(&mut self, other: &'a Self) {
        let y1y2 = self.y * other.y;
        let x1x2 = self.x * other.x;
        let dx1x2y1y2 = P::COEFF_D * y1y2 * x1x2;

        let d1 = P::BaseField::one() + dx1x2y1y2;
        let d2 = P::BaseField::one() - dx1x2y1y2;

        let x1y2 = self.x * other.y;
        let y1x2 = self.y * other.x;

        self.x = (x1y2 + y1x2) / d1;
        self.y = (y1y2 - P::mul_by_a(&x1x2)) / d2;
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for Affine<P> {
    type Output = Self;

    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for Affine<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: Parameters> Mul<P::ScalarField> for Affine<P> {
    type Output = Self;

    fn mul(self, other: P::ScalarField) -> Self {
        self.mul_bits(BitIteratorBE::new(other.to_repr())).into()
    }
}

impl<P: Parameters> MulAssign<P::ScalarField> for Affine<P> {
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = self.mul(other)
    }
}

impl<P: Parameters> ToBytes for Affine<P> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write_le(&mut writer)?;
        self.y.write_le(&mut writer)
    }
}

impl<P: Parameters> FromBytes for Affine<P> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read_le(&mut reader)?;
        let y = P::BaseField::read_le(&mut reader)?;
        Ok(Self::new(x, y))
    }
}

impl<P: Parameters> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> Distribution<Affine<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::from_x_coordinate(x, greatest) {
                return p.scale_by_cofactor().into();
            }
        }
    }
}

// The projective point X, Y, T, Z is represented in the affine
// coordinates as X/Z, Y/Z.
impl<P: Parameters> From<Projective<P>> for Affine<P> {
    fn from(p: Projective<P>) -> Affine<P> {
        if p.is_zero() {
            Affine::zero()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Affine::new(p.x, p.y)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let z_inv = p.z.inverse().unwrap();
            let x = p.x * z_inv;
            let y = p.y * z_inv;
            Affine::new(x, y)
        }
    }
}

impl_edwards_curve_serializer!(Parameters);
