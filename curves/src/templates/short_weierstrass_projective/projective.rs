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
    templates::short_weierstrass_projective::Affine,
    traits::{AffineCurve, Group, ProjectiveCurve, ShortWeierstrassParameters as Parameters},
};
use snarkvm_fields::{impl_add_sub_from_field_ref, Field, One, PrimeField, Zero};
use snarkvm_utilities::{
    bititerator::BitIteratorBE,
    bytes::{FromBytes, ToBytes},
    rand::UniformRand,
    serialize::*,
};

use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use std::{
    fmt::{Display, Formatter, Result as FmtResult},
    io::{Read, Result as IoResult, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

#[derive(Derivative)]
#[derivative(
    Copy(bound = "P: Parameters"),
    Clone(bound = "P: Parameters"),
    Eq(bound = "P: Parameters"),
    Debug(bound = "P: Parameters"),
    Hash(bound = "P: Parameters")
)]
pub struct Projective<P: Parameters> {
    pub x: P::BaseField,
    pub y: P::BaseField,
    pub z: P::BaseField,
}

impl<P: Parameters> Projective<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, z: P::BaseField) -> Self {
        Self { x, y, z }
    }
}

impl<P: Parameters> Display for Projective<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.into_affine())
    }
}

impl<P: Parameters> PartialEq for Projective<P> {
    fn eq(&self, other: &Self) -> bool {
        if self.is_zero() {
            return other.is_zero();
        }

        if other.is_zero() {
            return false;
        }

        // x1/z1 == x2/z2  <==> x1 * z2 == x2 * z1
        (self.x * other.z) == (other.x * self.z) && (self.y * other.z) == (other.y * self.z)
    }
}

impl<P: Parameters> Distribution<Projective<P>> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
        let res = Projective::prime_subgroup_generator() * P::ScalarField::rand(rng);
        debug_assert!(res.into_affine().is_in_correct_subgroup_assuming_on_curve());
        res
    }
}

impl<P: Parameters> ToBytes for Projective<P> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.x.write(&mut writer)?;
        self.y.write(&mut writer)?;
        self.z.write(writer)
    }
}

impl<P: Parameters> FromBytes for Projective<P> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read(&mut reader)?;
        let y = P::BaseField::read(&mut reader)?;
        let z = P::BaseField::read(reader)?;
        Ok(Self::new(x, y, z))
    }
}

impl<P: Parameters> Default for Projective<P> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl<P: Parameters> Zero for Projective<P> {
    // The point at infinity is always represented by Z = 0.
    #[inline]
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one(), P::BaseField::zero())
    }

    // The point at infinity is always represented by
    // Z = 0.
    #[inline]
    fn is_zero(&self) -> bool {
        self.z.is_zero()
    }
}

impl<P: Parameters> ProjectiveCurve for Projective<P> {
    type Affine = Affine<P>;
    type BaseField = P::BaseField;

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Affine::prime_subgroup_generator().into()
    }

    #[inline]
    fn is_normalized(&self) -> bool {
        self.is_zero() || self.z.is_one()
    }

    fn batch_normalization(v: &mut [Self]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        // First pass: compute [a, ab, abc, ...]
        let mut prod = Vec::with_capacity(v.len());
        let mut tmp = P::BaseField::one();
        for g in v
            .iter_mut()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
        {
            tmp.mul_assign(&g.z);
            prod.push(tmp);
        }

        // Invert `tmp`.
        tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

        // Second pass: iterate backwards to compute inverses
        for (g, s) in v
            .iter_mut()
            // Backwards
            .rev()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
            // Backwards, skip last element, fill in one for last term.
            .zip(
                prod.into_iter()
                    .rev()
                    .skip(1)
                    .chain(Some(P::BaseField::one())),
            )
        {
            // tmp := tmp * g.z; g.z := tmp * s = 1/z
            let newtmp = tmp * g.z;
            g.z = tmp * s;
            tmp = newtmp;
        }

        // Perform affine transformations
        for g in v.iter_mut().filter(|g| !g.is_normalized()) {
            g.x *= &g.z; // x/z^2
            g.y *= &g.z;
            g.z = P::BaseField::one(); // z = 1
        }
    }

    fn add_assign_mixed(&mut self, other: &Self::Affine) {
        if other.is_zero() {
            return;
        } else if self.is_zero() {
            self.x = other.x;
            self.y = other.y;
            self.z = P::BaseField::one();
            return;
        }
        let mut v = other.x * self.z;
        let mut u = other.y * self.z;
        if u == self.y && v == self.x {
            // x1 / z1 == x2 / z2 <==> x1 * z2 == x2 * z1;
            // Here, z2 = 1, so we have x1 == x2 * z1;
            self.double_in_place();
        } else {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-madd-1998-cmo
            // u = Y2*Z1-Y1
            u -= &self.y;
            // uu = u^2
            let uu = u.square();
            // v = X2*Z1-X1
            v -= &self.x;
            // vv = v2
            let vv = v.square();
            // vvv = v*vv
            let vvv = v * vv;
            // r = vv*X1
            let r = vv * self.x;
            // a = uu*Z1-vvv-2*r
            let a = uu * self.z - vvv - r.double();
            // X3 = v*a
            self.x = v * a;
            // Y3 = u*(R-A)-vvv*Y1
            self.y = u * (r - a) - (vvv * self.y);
            // Z3 = vvv*Z1
            self.z = vvv * self.z;
        }
    }

    fn into_affine(&self) -> Affine<P> {
        (*self).into()
    }

    fn recommended_wnaf_for_scalar(scalar: <Self::ScalarField as PrimeField>::BigInteger) -> usize {
        P::empirical_recommended_wnaf_for_scalar(scalar)
    }

    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        P::empirical_recommended_wnaf_for_num_scalars(num_scalars)
    }
}

impl<P: Parameters> Group for Projective<P> {
    type ScalarField = P::ScalarField;

    #[inline]
    #[must_use]
    fn double(&self) -> Self {
        let mut tmp = *self;
        tmp.double_in_place();
        tmp
    }

    #[inline]
    fn double_in_place(&mut self) {
        if self.is_zero() {
            return;
        } else {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#doubling-dbl-2007-bl

            // XX = X1^2
            let xx = self.x.square();
            // ZZ = Z1^2
            let zz = self.z.square();
            // w = a*ZZ + 3*XX
            let w = P::mul_by_a(&zz) + (xx + xx.double());
            // s = 2*Y1*Z1
            let mut s = self.y * (self.z);
            s.double_in_place();
            // sss = s^3
            let mut sss = s.square();
            sss *= &s;
            // R = Y1*s
            let r = self.y * s;
            // RR = R2
            let rr = r.square();
            // B = (X1+R)^2-XX-RR
            let b = (self.x + r).square() - xx - rr;
            // h = w2-2*B
            let h = w.square() - (b + b);
            // X3 = h*s
            self.x = h * s;
            // Y3 = w*(B-h)-2*RR
            self.y = w * (b - h) - (rr + rr);
            // Z3 = sss
            self.z = sss;
        }
    }
}

impl<P: Parameters> Neg for Projective<P> {
    type Output = Self;

    fn neg(self) -> Self {
        if !self.is_zero() {
            Self::new(self.x, -self.y, self.z)
        } else {
            self
        }
    }
}

impl_add_sub_from_field_ref!(Projective, Parameters);

impl<'a, P: Parameters> Add<&'a Self> for Projective<P> {
    type Output = Self;

    fn add(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy += other;
        copy
    }
}

impl<'a, P: Parameters> AddAssign<&'a Self> for Projective<P> {
    #[allow(clippy::suspicious_op_assign_impl)]
    fn add_assign(&mut self, other: &'a Self) {
        if self.is_zero() {
            *self = *other;
            return;
        }

        if other.is_zero() {
            return;
        }
        // https://www.hyperelliptic.org/EFD/g1p/data/shortw/projective/addition/add-1998-cmo-2

        if self == other {
            self.double_in_place();
        } else {
            // Y1Z2 = Y1*Z2
            let y1z2 = self.y * other.z;
            // X1Z2 = X1*Z2
            let x1z2 = self.x * other.z;
            // Z1Z2 = Z1*Z2
            let z1z2 = self.z * other.z;
            // u = Y2*Z1-Y1Z2
            let u = (self.z * other.y) - y1z2;
            // uu = u^2
            let uu = u.square();
            // v = X2*Z1-X1Z2
            let v = (self.z * other.x) - x1z2;
            // vv = v^2
            let vv = v.square();
            // vvv = v*vv
            let vvv = v * vv;
            // R = vv*X1Z2
            let r = vv * x1z2;
            // A = uu*Z1Z2-vvv-2*R
            let a = (uu * z1z2) - (vvv + r + r);
            // X3 = v*A
            self.x = v * a;
            // Y3 = u*(R-A)-vvv*Y1Z2
            self.y = ((r - a) * u) - (vvv * y1z2);
            // Z3 = vvv*Z1Z2
            self.z = vvv * z1z2;
        }
    }
}

impl<'a, P: Parameters> Sub<&'a Self> for Projective<P> {
    type Output = Self;

    fn sub(self, other: &'a Self) -> Self {
        let mut copy = self;
        copy -= other;
        copy
    }
}

impl<'a, P: Parameters> SubAssign<&'a Self> for Projective<P> {
    fn sub_assign(&mut self, other: &'a Self) {
        *self += &(-(*other));
    }
}

impl<P: Parameters> Mul<P::ScalarField> for Projective<P> {
    type Output = Self;

    /// Performs scalar multiplication of this element.
    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn mul(self, other: P::ScalarField) -> Self {
        let mut res = Self::zero();

        let mut found_one = false;

        for i in BitIteratorBE::new(other.into_repr()) {
            if found_one {
                res.double_in_place();
            } else {
                found_one = i;
            }

            if i {
                res += self;
            }
        }

        res
    }
}

impl<P: Parameters> MulAssign<P::ScalarField> for Projective<P> {
    /// Performs scalar multiplication of this element.
    fn mul_assign(&mut self, other: P::ScalarField) {
        *self = *self * other
    }
}

// The affine point X, Y is represented in the jacobian
// coordinates with Z = 1.
impl<P: Parameters> From<Affine<P>> for Projective<P> {
    fn from(p: Affine<P>) -> Projective<P> {
        if p.is_zero() {
            Self::zero()
        } else {
            Self::new(p.x, p.y, P::BaseField::one())
        }
    }
}
