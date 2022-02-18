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
    impl_sw_curve_serializer,
    templates::short_weierstrass_jacobian::Projective,
    traits::{AffineCurve, Group, ProjectiveCurve, ShortWeierstrassParameters as Parameters},
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
    io::{Error, ErrorKind, Read, Result as IoResult, Write},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// A macro which computes:
///     `lambda` := `(y2 - y1) / (x2 - x1)`,
/// for two given affine points.
macro_rules! batch_add_loop_1 {
    ($a: ident, $b: ident, $half: ident, $inversion_tmp: ident) => {
        if $a.is_zero() || $b.is_zero() {
            ();
        } else if $a.x == $b.x {
            // Double
            // In our model, we consider self additions rare.
            // So we consider it inconsequential to make them more expensive
            // This costs 1 modular mul more than a standard squaring,
            // and one amortised inversion
            if $a.y == $b.y {
                // Compute one half (1/2) and cache it.
                $half = match $half {
                    None => P::BaseField::one().double().inverse(),
                    _ => $half,
                };
                let h = $half.unwrap();

                let x_sq = $b.x.square();
                $b.x -= &$b.y; // x - y
                $a.x = $b.y.double(); // denominator = 2y
                $a.y = x_sq.double() + &x_sq + &P::COEFF_A; // numerator = 3x^2 + a
                $b.y -= &(h * &$a.y); // y - (3x^2 + a)/2
                $a.y *= &$inversion_tmp; // (3x^2 + a) * tmp
                $inversion_tmp *= &$a.x; // update tmp
            } else {
                // No inversions take place if either operand is zero
                $a.infinity = true;
                $b.infinity = true;
            }
        } else {
            // We can recover x1 + x2 from this. Note this is never 0.
            $a.x -= &$b.x; // denominator = x1 - x2
            $a.y -= &$b.y; // numerator = y1 - y2
            $a.y *= &$inversion_tmp; // (y1 - y2)*tmp
            $inversion_tmp *= &$a.x // update tmp
        }
    };
}

/// A macro which computes:
///     `x3` := `lambda^2 - x1 - x2`
///     `y3` := `lambda * (x1 - x3) - y1`.
macro_rules! batch_add_loop_2 {
    ($a: ident, $b: ident, $inversion_tmp: ident) => {
        if $a.is_zero() {
            *$a = $b;
        } else if !$b.is_zero() {
            let lambda = $a.y * &$inversion_tmp;
            $inversion_tmp *= &$a.x; // Remove the top layer of the denominator

            // x3 = l^2 - x1 - x2 or for squaring: 2y + l^2 + 2x - 2y = l^2 - 2x
            $a.x += &$b.x.double();
            $a.x = lambda.square() - &$a.x;
            // y3 = l*(x2 - x3) - y2 or
            // for squaring: (3x^2 + a)/2y(x - y - x3) - (y - (3x^2 + a)/2) = l*(x - x3) - y
            $a.y = lambda * &($b.x - &$a.x) - &$b.y;
        }
    };
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
    pub infinity: bool,
}

impl<P: Parameters> Affine<P> {
    pub fn new(x: P::BaseField, y: P::BaseField, infinity: bool) -> Self {
        Self { x, y, infinity }
    }

    pub fn scale_by_cofactor(&self) -> Projective<P> {
        self.mul_bits(BitIteratorBE::new(P::COFACTOR))
    }
}

impl<P: Parameters> Zero for Affine<P> {
    #[inline]
    fn zero() -> Self {
        Self::new(P::BaseField::zero(), P::BaseField::one(), true)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl<P: Parameters> Display for Affine<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        if self.infinity { write!(f, "Affine(Infinity)") } else { write!(f, "Affine(x={}, y={})", self.x, self.y) }
    }
}

impl<P: Parameters> PartialEq<Projective<P>> for Affine<P> {
    fn eq(&self, other: &Projective<P>) -> bool {
        other.eq(self)
    }
}

impl<P: Parameters> AffineCurve for Affine<P> {
    type BaseField = P::BaseField;
    type Projective = Projective<P>;

    #[inline]
    fn prime_subgroup_generator() -> Self {
        Self::new(P::AFFINE_GENERATOR_COEFFS.0, P::AFFINE_GENERATOR_COEFFS.1, false)
    }

    #[inline]
    fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
        Self::BaseField::from_random_bytes_with_flags::<SWFlags>(bytes).and_then(|(x, flags)| {
            // If x is valid and is zero and only the infinity flag is set, then parse this
            // point as infinity. For all other choices, get the original point.
            if x.is_zero() && flags.is_infinity() {
                Some(Self::zero())
            } else if let Some(is_positive_y) = flags.is_positive() {
                Self::from_x_coordinate(x, is_positive_y) // Unwrap is safe because it's not zero.
            } else {
                None
            }
        })
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    fn from_x_coordinate(x: Self::BaseField, greatest: bool) -> Option<Self> {
        // Compute x^3 + ax + b
        let x3b = P::add_b(&((x.square() * x) + P::mul_by_a(&x)));

        x3b.sqrt().map(|y| {
            let negy = -y;

            let y = if (y < negy) ^ greatest { y } else { negy };
            Self::new(x, y, false)
        })
    }

    /// Attempts to construct an affine point given a y-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    fn from_y_coordinate(_y: Self::BaseField, _greatest: bool) -> Option<Self> {
        unimplemented!()
    }

    fn mul_bits(&self, bits: impl Iterator<Item = bool>) -> Projective<P> {
        let mut output = Projective::zero();
        for i in bits {
            output.double_in_place();
            if i {
                output.add_assign_mixed(self);
            }
        }
        output
    }

    fn mul_by_cofactor_to_projective(&self) -> Self::Projective {
        self.scale_by_cofactor()
    }

    fn mul_by_cofactor_inv(&self) -> Self {
        self.mul(P::COFACTOR_INV)
    }

    #[inline]
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
        if self.is_zero() {
            true
        } else {
            // Check that the point is on the curve
            let y2 = self.y.square();
            let x3b = P::add_b(&((self.x.square() * self.x) + P::mul_by_a(&self.x)));
            y2 == x3b
        }
    }

    #[inline]
    fn batch_add_in_place_same_slice(bases: &mut [Self], index: &[(u32, u32)]) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            let (mut a, mut b) = if idx < idy {
                let (x, y) = bases.split_at_mut(*idy as usize);
                (&mut x[*idx as usize], &mut y[0])
            } else {
                let (x, y) = bases.split_at_mut(*idx as usize);
                (&mut y[0], &mut x[*idy as usize])
            };
            batch_add_loop_1!(a, b, half, inversion_tmp);
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        for (idx, idy) in index.iter().rev() {
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

    fn batch_add_write(
        bases: &[Self],
        index: &[(u32, u32)],
        new_bases: &mut Vec<Self>,
        scratch_space: &mut Vec<Option<Self>>,
    ) {
        let mut inversion_tmp = P::BaseField::one();
        let mut half = None;

        // We run two loops over the data separated by an inversion
        for (idx, idy) in index.iter() {
            if *idy == !0u32 {
                new_bases.push(bases[*idx as usize]);
                scratch_space.push(None);
            } else {
                let (mut a, mut b) = (bases[*idx as usize], bases[*idy as usize]);
                batch_add_loop_1!(a, b, half, inversion_tmp);
                new_bases.push(a);
                scratch_space.push(Some(b));
            }
        }

        inversion_tmp = inversion_tmp.inverse().unwrap(); // this is always in Fp*

        for (a, op_b) in new_bases.iter_mut().rev().zip(scratch_space.iter().rev()) {
            match op_b {
                Some(b) => {
                    let b_ = *b;
                    batch_add_loop_2!(a, b_, inversion_tmp);
                }
                None => (),
            };
        }
        scratch_space.clear();
    }
}

impl<P: Parameters> ToMinimalBits for Affine<P> {
    fn to_minimal_bits(&self) -> Vec<bool> {
        let mut res_bits = self.x.to_bits_le();
        res_bits.push(*self.y.to_bits_le().first().unwrap());
        res_bits.push(self.infinity);
        res_bits
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

    #[inline]
    fn neg(self) -> Self {
        if !self.is_zero() { Self::new(self.x, -self.y, false) } else { self }
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
    fn add_assign(&mut self, other: &'a Self) {
        let mut projective = Projective::from(*self);
        projective.add_assign_mixed(other);
        *self = projective.into();
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
        self.y.write_le(&mut writer)?;
        self.infinity.write_le(writer)
    }
}

impl<P: Parameters> FromBytes for Affine<P> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let x = P::BaseField::read_le(&mut reader)?;
        let y = P::BaseField::read_le(&mut reader)?;
        let infinity = bool::read_le(&mut reader)?;

        if infinity != x.is_zero() && y.is_one() {
            return Err(Error::new(ErrorKind::InvalidData, "Infinity flag is not valid"));
        }
        Ok(Self::new(x, y, infinity))
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

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl<P: Parameters> From<Projective<P>> for Affine<P> {
    #[inline]
    fn from(p: Projective<P>) -> Affine<P> {
        if p.is_zero() {
            Affine::zero()
        } else if p.z.is_one() {
            // If Z is one, the point is already normalized.
            Affine::new(p.x, p.y, false)
        } else {
            // Z is nonzero, so it must have an inverse in a field.
            let zinv = p.z.inverse().unwrap();
            let zinv_squared = zinv.square();

            // X/Z^2
            let x = p.x * zinv_squared;

            // Y/Z^3
            let y = p.y * (zinv_squared * zinv);

            Affine::new(x, y, false)
        }
    }
}

impl_sw_curve_serializer!(Parameters);
