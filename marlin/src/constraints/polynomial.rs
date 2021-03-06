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

use crate::PhantomData;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::traits::fields::FieldGadget;
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

/// A struct with methods to compute vanishing polynomial equations.
pub struct AlgebraForAHP<F: PrimeField, CF: PrimeField> {
    field: PhantomData<F>,
    constraint_field: PhantomData<CF>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> AlgebraForAHP<TargetField, BaseField> {
    /// Returns `x^domain_size`.
    pub fn prepare<CS: ConstraintSystem<BaseField>>(
        cs: CS,
        x: &NonNativeFieldVar<TargetField, BaseField>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        x.pow_by_constant(cs, &[domain_size])
    }

    /// Returns `x_prepared - 1`.
    pub fn prepared_eval_vanishing_polynomial<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        x_prepared: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let one = NonNativeFieldVar::<TargetField, BaseField>::one(cs.ns(|| "one"))?;
        let result = x_prepared.sub(cs.ns(|| "x_prepared_minus_one"), &one)?;
        Ok(result)
    }

    /// Returns `x^domain_size - 1`.
    pub fn eval_vanishing_polynomial<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        x: &NonNativeFieldVar<TargetField, BaseField>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let x_prepared = Self::prepare(cs.ns(|| "x_prepared"), x, domain_size)?;
        Self::prepared_eval_vanishing_polynomial(cs, &x_prepared)
    }

    /// Returns `x^domain_size - 1`.
    pub fn prepared_eval_bivariable_vanishing_polynomial<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        x: &NonNativeFieldVar<TargetField, BaseField>,
        y: &NonNativeFieldVar<TargetField, BaseField>,
        x_prepared: &NonNativeFieldVar<TargetField, BaseField>,
        y_prepared: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        // Compute `x - y`.
        let denominator = x.sub(cs.ns(|| "denominator"), &y)?;

        // Compute `x_prepared - y_prepared`.
        let numerator = x_prepared.sub(cs.ns(|| "numerator"), &y_prepared)?;
        let denominator_invert = denominator.inverse(cs.ns(|| "denominator_inverse"))?;

        // Compute `(x - y) / (x_prepared - y_prepared)`.
        let result = numerator.mul(cs.ns(|| "numerator_over_denominator"), &denominator_invert)?;
        Ok(result)
    }

    /// Returns `(x - y) / ((x^domain_size - 1) - (y^domain_size - 1))`.
    pub fn eval_bivariate_vanishing_polynomial<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        x: &NonNativeFieldVar<TargetField, BaseField>,
        y: &NonNativeFieldVar<TargetField, BaseField>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let x_prepared = Self::prepare(cs.ns(|| "x_prepared"), x, domain_size)?;
        let y_prepared = Self::prepare(cs.ns(|| "y_prepared"), y, domain_size)?;

        Self::prepared_eval_bivariable_vanishing_polynomial(cs, x, y, &x_prepared, &y_prepared)
    }
}
