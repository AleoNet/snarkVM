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

use crate::{curves::templates::bls12::AffineGadget, Boolean, CondSelectGadget, FieldGadget};
use snarkvm_curves::SWModelParameters;
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use std::marker::PhantomData;

/// The original arkworks-rs version: https://github.com/arkworks-rs/r1cs-std/blob/master/src/groups/curves/short_weierstrass/non_zero_affine.rs
/// adapted to the Zexe/snarkVM API.

/// An affine representation of a prime order curve point that is guaranteed
/// to *not* be the point at infinity.
#[derive(Derivative)]
#[derivative(Debug, Clone)]
#[must_use]
pub struct NonZeroAffineVar<P: SWModelParameters, F: Field, FG: FieldGadget<P::BaseField, F>> {
    /// The x-coordinate.
    pub x: FG,
    /// The y-coordinate.
    pub y: FG,
    #[derivative(Debug = "ignore")]
    _parameters: PhantomData<P>,
    _engine: PhantomData<F>,
}

impl<P: SWModelParameters, F: Field, FG: FieldGadget<P::BaseField, F>> NonZeroAffineVar<P, F, FG> {
    pub fn new(x: FG, y: FG) -> Self {
        Self {
            x,
            y,
            _parameters: PhantomData,
            _engine: PhantomData,
        }
    }

    /// Converts self into a classical affine point.
    pub fn into_classical_affine(&self) -> AffineGadget<P, F, FG> {
        AffineGadget::<P, F, FG>::new(self.x.clone(), self.y.clone(), Boolean::Constant(false))
    }

    /// Performs an addition without checking that other != ±self.
    pub fn add_unchecked<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let (x1, y1) = (&self.x, &self.y);
        let (x2, y2) = (&other.x, &other.y);

        // Then,
        // slope lambda := (y2 - y1)/(x2 - x1);
        // x3 = lambda^2 - x1 - x2;
        // y3 = lambda * (x1 - x3) - y1
        let numerator = y2.sub(cs.ns(|| "y2 - y1"), &y1)?;
        let denominator = x2.sub(cs.ns(|| "x2 - x2"), x1)?;

        let lambda = numerator.mul_by_inverse(cs.ns(|| "lambda"), &denominator)?;
        let x3 = lambda
            .square(cs.ns(|| "lambda^2"))?
            .sub(cs.ns(|| "lambda - x1"), &x1)?
            .sub(cs.ns(|| "lambda - x1 - x2"), &x2)?;
        let x1_minus_x3 = x1.sub(cs.ns(|| "x1 - x3"), &x3)?;
        let y3 = lambda
            .mul(cs.ns(|| "lambda * (x1 - x3)"), &x1_minus_x3)?
            .sub(cs.ns(|| "y3"), &y1)?;
        Ok(Self::new(x3, y3))
    }

    /// Doubles `self`. As this is a prime order curve point,
    /// the output is guaranteed to not be the point at infinity.
    pub fn double<CS: ConstraintSystem<F>>(&self, mut cs: CS) -> Result<Self, SynthesisError> {
        let (x1, y1) = (&self.x, &self.y);
        let x1_sqr = x1.square(cs.ns(|| "x1^2"))?;
        // Then,
        // tangent lambda := (3 * x1^2 + a) / (2 * y1);
        // x3 = lambda^2 - 2x1
        // y3 = lambda * (x1 - x3) - y1
        let numerator = x1_sqr
            .double(cs.ns(|| "x1^2 * 2"))?
            .add(cs.ns(|| "x1^2 * 3"), &x1_sqr)?
            .add_constant(cs.ns(|| "3 * x1^2 + a"), &P::COEFF_A)?;
        let denominator = y1.double(cs.ns(|| "2 * y1"))?;
        let lambda = numerator.mul_by_inverse(cs.ns(|| "lambda"), &denominator)?;
        let x1_double = x1.double(cs.ns(|| "2 x1"))?;
        let x3 = lambda.square(cs.ns(|| "lambda^2"))?.sub(cs.ns(|| "x3"), &x1_double)?;
        let x1_minus_x3 = x1.sub(cs.ns(|| "x1 - x3"), &x3)?;
        let y3 = lambda
            .mul(cs.ns(|| "lambda * (x1 - x3)"), &x1_minus_x3)?
            .sub(cs.ns(|| "y3"), &y1)?;
        Ok(Self::new(x3, y3))
    }

    /// Computes `(self + other) + self`. This method requires only 5 constraints,
    /// less than the 7 required when computing via `self.double() + other`.
    ///
    /// Requires that `other != ±self`.
    ///
    /// This follows the formulae from [\[ELM03\]](https://arxiv.org/abs/math/0208038).
    pub fn double_and_add<CS: ConstraintSystem<F>>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError> {
        let (x1, y1) = (&self.x, &self.y);
        let (x2, y2) = (&other.x, &other.y);

        // Calculate self + other:
        // slope lambda := (y2 - y1)/(x2 - x1);
        // x3 = lambda^2 - x1 - x2;
        // y3 = lambda * (x1 - x3) - y1
        let numerator = y2.sub(cs.ns(|| "y2 - y1"), &y1)?;
        let denominator = x2.sub(cs.ns(|| "x2 - x1"), &x1)?;

        let lambda_1 = numerator.mul_by_inverse(cs.ns(|| "lambda_1"), &denominator)?;
        let x3 = lambda_1
            .square(cs.ns(|| "lambda_1 ^2"))?
            .sub(cs.ns(|| "lambda_1 ^2 - x1"), &x1)?
            .sub(cs.ns(|| "x3"), &x2)?;

        // Calculate final addition slope:
        // tmp = y1 * 2 / (x3 - x1)
        let x3_minus_x1 = x3.sub(cs.ns(|| "x3 - x1"), &x1)?;
        let tmp = y1
            .double(cs.ns(|| "y1 * 2"))?
            .mul_by_inverse(cs.ns(|| "y1 * 2 div by (x3 - x1)"), &x3_minus_x1)?;
        let lambda_2 = lambda_1
            .add(cs.ns(|| "lambda_1 + tmp"), &tmp)?
            .negate(cs.ns(|| "lambda_2"))?;

        let x4 = lambda_2
            .square(cs.ns(|| "lambda_2 ^2"))?
            .sub(cs.ns(|| "lambda_2 ^2 - x1"), &x1)?
            .sub(cs.ns(|| "x4"), &x3)?;
        let x1_minus_x4 = x1.sub(cs.ns(|| "x1 - x4"), &x4)?;
        let y4 = lambda_2
            .mul(cs.ns(|| "lambda_2 * (x1 - x4)"), &x1_minus_x4)?
            .sub(cs.ns(|| "y4"), &y1)?;
        Ok(Self::new(x4, y4))
    }

    /// Doubles `self` in place.
    pub fn double_in_place<CS: ConstraintSystem<F>>(&mut self, cs: CS) -> Result<(), SynthesisError> {
        *self = self.double(cs)?;
        Ok(())
    }
}

impl<P: SWModelParameters, F: Field, FG: FieldGadget<P::BaseField, F>> CondSelectGadget<F>
    for NonZeroAffineVar<P, F, FG>
{
    fn conditionally_select<CS: ConstraintSystem<F>>(
        mut cs: CS,
        cond: &Boolean,
        first: &Self,
        second: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = FG::conditionally_select(cs.ns(|| "x"), cond, &first.x, &second.x)?;
        let y = FG::conditionally_select(cs.ns(|| "y"), cond, &first.y, &second.y)?;

        Ok(Self::new(x, y))
    }

    fn cost() -> usize {
        2 * <FG as CondSelectGadget<F>>::cost()
    }
}
