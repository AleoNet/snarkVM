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
    impl_edwards_curve_serializer,
    templates::twisted_edwards_extended::Projective,
    traits::{AffineCurve, ProjectiveCurve, TwistedEdwardsParameters as Parameters},
};
use snarkvm_fields::{Field, One, PrimeField, SquareRootField, Zero};
use snarkvm_utilities::{
    bititerator::BitIteratorBE,
    io::{Read, Result as IoResult, Write},
    rand::Uniform,
    serialize::*,
    FromBytes,
    ToBits,
    ToBytes,
    ToMinimalBits,
};

use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    ops::{Mul, Neg},
};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use serde::{Deserialize, Serialize};

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
    #[inline]
    pub const fn new(x: P::BaseField, y: P::BaseField) -> Self {
        Self { x, y }
    }
}

impl<P: Parameters> Zero for Affine<P> {
    #[inline]
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one())
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.x.is_zero() & self.y.is_one()
    }
}

impl<P: Parameters> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        other.eq(self)
    }
}

impl<P: Parameters> Default for Affine<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "Affine(x={}, y={})", self.x, self.y)
    }
}

impl<P: Parameters> AffineCurve for Affine<P> {
    type BaseField = P::BaseField;
    type Coordinates = (Self::BaseField, Self::BaseField);
    type Projective = Projective<P>;
    type ScalarField = P::ScalarField;

    /// Initializes a new affine group element from the given coordinates.
    fn from_coordinates(coordinates: Self::Coordinates) -> Self {
        let (x, y) = coordinates;
        let point = Self { x, y };
        assert!(point.is_on_curve());
        point
    }

    #[inline]
    fn cofactor() -> &'static [u64] {
        P::COFACTOR
    }

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
        self.mul_bits(BitIteratorBE::new(P::COFACTOR))
    }

    fn mul_by_cofactor_inv(&self) -> Self {
        (*self * P::COFACTOR_INV).into()
    }

    fn to_projective(&self) -> Projective<P> {
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

    /// Performs the first half of batch addition in-place.
    fn batch_add_loop_1(a: &mut Self, b: &mut Self, _half: &Self::BaseField, inversion_tmp: &mut Self::BaseField) {
        if !a.is_zero() && !b.is_zero() {
            let y1y2 = a.y * b.y;
            let x1x2 = a.x * b.x;

            a.x = (a.x + a.y) * (b.x + b.y) - y1y2 - x1x2;
            a.y = y1y2;
            if !P::COEFF_A.is_zero() {
                a.y -= &P::mul_by_a(&x1x2);
            }

            let dx1x2y1y2 = P::COEFF_D * y1y2 * x1x2;

            let inversion_mul_d = *inversion_tmp * dx1x2y1y2;

            a.x *= &(*inversion_tmp - inversion_mul_d);
            a.y *= &(*inversion_tmp + inversion_mul_d);

            b.x = Self::BaseField::one() - dx1x2y1y2.square();

            *inversion_tmp *= &b.x;
        }
    }

    /// Performs the second half of batch addition in-place.
    fn batch_add_loop_2(a: &mut Self, b: Self, inversion_tmp: &mut Self::BaseField) {
        if a.is_zero() {
            *a = b;
        } else if !b.is_zero() {
            a.x *= *inversion_tmp;
            a.y *= *inversion_tmp;
            *inversion_tmp *= &b.x;
        }
    }
}

impl<P: Parameters> ToMinimalBits for Affine<P> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        self.x.to_bits_le()
    }
}

impl<P: Parameters> Neg for Affine<P> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.x, self.y)
    }
}

impl<P: Parameters> Mul<P::ScalarField> for Affine<P> {
    type Output = Projective<P>;

    fn mul(self, other: P::ScalarField) -> Self::Output {
        self.mul_bits(BitIteratorBE::new(other.to_repr()))
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

impl<P: Parameters> Distribution<Affine<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
        loop {
            let x = P::BaseField::rand(rng);
            let greatest = rng.gen();

            if let Some(p) = Affine::from_x_coordinate(x, greatest) {
                return p.mul_by_cofactor();
            }
        }
    }
}

// The projective point X, Y, T, Z is represented in the affine coordinates as X/Z, Y/Z.
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
