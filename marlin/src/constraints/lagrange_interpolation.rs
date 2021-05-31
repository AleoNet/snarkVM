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

use snarkvm_fields::{batch_inversion, Field, PrimeField};
use snarkvm_gadgets::{
    nonnative::NonNativeFieldVar,
    traits::{alloc::AllocGadget, eq::EqGadget, fields::FieldGadget},
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::constraints::polynomial::AlgebraForAHP;

/// A helper struct for evaluating the vanishing polynomial.
pub struct VanishingPolynomial<F: Field> {
    constant_term: F,
    order_h: u64,
}

impl<F: Field> VanishingPolynomial<F> {
    /// Instantiates a new instance of the `VanishingPolynomial`.
    pub fn new(offset: F, order_h: u64) -> Self {
        VanishingPolynomial {
            constant_term: offset.pow([order_h]),
            order_h,
        }
    }

    /// Evaluates the vanishing polynomial for a given field value `x` and domain of order `h`.
    pub fn evaluate(&self, x: &F) -> F {
        let mut result = x.pow([self.order_h]);
        result -= &self.constant_term;
        result
    }
}

/// A Lagrange interpolation struct for field elements.
pub struct LagrangeInterpolator<F: PrimeField> {
    all_domain_elems: Vec<F>,
    v_inv_elems: Vec<F>,
    domain_vp: VanishingPolynomial<F>,
    poly_evaluations: Vec<F>,
}

impl<BaseField: PrimeField> LagrangeInterpolator<BaseField> {
    /// Instantiates a new instance of the `LagrangeInterpolator`.
    pub fn new(domain_generator: BaseField, domain_order: u64, polynomial_evaluations: Vec<BaseField>) -> Self {
        let num_polynomial_evaluations = polynomial_evaluations.len();

        let mut current_element = domain_generator;
        let mut all_domain_elems = vec![BaseField::one()];
        let mut v_inv_elems: Vec<BaseField> = Vec::new();

        for _ in 1..num_polynomial_evaluations {
            all_domain_elems.push(current_element);
            current_element *= &domain_generator;
        }

        let g_inv = domain_generator.inverse().unwrap();
        let m = BaseField::from(domain_order as u128);
        let mut v_inv_i = m;
        for _ in 0..num_polynomial_evaluations {
            v_inv_elems.push(v_inv_i);
            v_inv_i *= &g_inv;
        }

        let vp = VanishingPolynomial::new(domain_generator, domain_order);

        let lagrange_interpolation: LagrangeInterpolator<BaseField> = LagrangeInterpolator {
            all_domain_elems,
            v_inv_elems,
            domain_vp: vp,
            poly_evaluations: polynomial_evaluations,
        };
        lagrange_interpolation
    }

    /// Returns the Lagrange coefficients.
    fn compute_lagrange_coefficients(&self, interpolation_point: BaseField) -> Vec<BaseField> {
        let poly_evaluations_size = self.poly_evaluations.len();

        let vp_t_inv = self.domain_vp.evaluate(&interpolation_point).inverse().unwrap();
        let mut inverted_lagrange_coeffs: Vec<BaseField> = Vec::with_capacity(self.all_domain_elems.len());
        for i in 0..poly_evaluations_size {
            let l = vp_t_inv * &self.v_inv_elems[i];
            let r = self.all_domain_elems[i];
            inverted_lagrange_coeffs.push(l * &(interpolation_point - &r));
        }
        let lagrange_coeffs = inverted_lagrange_coeffs.as_mut_slice();
        batch_inversion::<BaseField>(lagrange_coeffs);

        lagrange_coeffs.to_vec()
    }

    /// Returns the interpolated value for a given point.
    pub fn interpolate(&self, interpolation_point: BaseField) -> BaseField {
        let poly_evaluations_size = self.poly_evaluations.len();

        let lagrange_coeffs = self.compute_lagrange_coefficients(interpolation_point);
        let mut interpolation = BaseField::zero();

        for (lagrange_coeff, poly_evaluation) in lagrange_coeffs
            .iter()
            .zip(self.poly_evaluations.iter())
            .take(poly_evaluations_size)
        {
            interpolation += &(*lagrange_coeff * &poly_evaluation);
        }
        interpolation
    }
}

/// A Lagrange interpolation gadget for nonnative field elements.
pub struct LagrangeInterpolationVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// The native lagrange interpolation struct.
    pub lagrange_interpolator: LagrangeInterpolator<TargetField>,
    /// The vanishing polynomial at t.
    pub vp_t: Option<NonNativeFieldVar<TargetField, BaseField>>,
    poly_evaluations: Vec<NonNativeFieldVar<TargetField, BaseField>>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> LagrangeInterpolationVar<TargetField, BaseField> {
    /// Instantiates a new instance of the `LagrangeInterpolationVar`.
    pub fn new(
        domain_generator: TargetField,
        domain_dimension: u64,
        polynomial_evaluations: &[NonNativeFieldVar<TargetField, BaseField>],
    ) -> Self {
        let num_polynomial_evaluations = polynomial_evaluations.len();

        let mut poly_evaluations_cf: Vec<TargetField> = Vec::new();
        for poly_evaluation in polynomial_evaluations.iter().take(num_polynomial_evaluations) {
            poly_evaluations_cf.push(poly_evaluation.value().unwrap_or_default());
        }

        let lagrange_interpolator: LagrangeInterpolator<TargetField> =
            LagrangeInterpolator::new(domain_generator, domain_dimension, poly_evaluations_cf);

        LagrangeInterpolationVar {
            lagrange_interpolator,
            vp_t: None,
            poly_evaluations: (*polynomial_evaluations).to_vec(),
        }
    }

    /// Returns the Lagrange coefficients as nonnative field gadgets.
    fn compute_lagrange_coefficients_constraints<CS: ConstraintSystem<BaseField>>(
        &mut self,
        mut cs: CS,
        interpolation_point: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<Vec<NonNativeFieldVar<TargetField, BaseField>>, SynthesisError> {
        let num_polynomial_evaluations = self.poly_evaluations.len();

        let t = interpolation_point.clone();
        let lagrange_coeffs = self
            .lagrange_interpolator
            .compute_lagrange_coefficients(t.value().unwrap_or_default());

        let mut lagrange_coeffs_fg: Vec<NonNativeFieldVar<TargetField, BaseField>> = Vec::new();

        let vp_t = if self.vp_t.is_some() {
            self.vp_t.clone().unwrap()
        } else {
            AlgebraForAHP::<TargetField, BaseField>::eval_vanishing_polynomial(
                cs.ns(|| "evaluate_vanishing_polynomial"),
                &t,
                self.lagrange_interpolator.domain_vp.order_h,
            )?
        };

        if self.vp_t.is_none() {
            self.vp_t = Some(vp_t.clone());
        }

        for (i, ((all_domain_elem, v_inverse), lagrange_coefficient)) in self
            .lagrange_interpolator
            .all_domain_elems
            .iter()
            .zip(self.lagrange_interpolator.v_inv_elems.iter())
            .zip(lagrange_coeffs.iter())
            .take(num_polynomial_evaluations)
            .enumerate()
        {
            let domain: TargetField = -*all_domain_elem;

            let lagrange_coefficient = NonNativeFieldVar::<TargetField, BaseField>::alloc(
                cs.ns(|| format!("generate_lagrange_coefficient_{}", i)),
                || Ok(*lagrange_coefficient),
            )?;
            lagrange_coeffs_fg.push(lagrange_coefficient.clone());

            let t_minus_domain = t.add_constant(cs.ns(|| format!("t_minus_domain_{}", i)), &domain)?;
            let t_minus_domain_div_v =
                &t_minus_domain.mul_by_constant(cs.ns(|| format!("t_minus_domain_div_v_{}", i)), v_inverse)?;
            let test_elem = t_minus_domain_div_v.mul(
                cs.ns(|| format!("t_minus_domain_div_v_mul_lag_coeff_{}", i)),
                &lagrange_coefficient,
            )?;
            test_elem.enforce_equal(cs.ns(|| format!("enforce_equal_{}", i)), &vp_t)?;
        }
        Ok(lagrange_coeffs_fg)
    }

    /// Returns the interpolated value as a nonnative field gadget for a given nonnative field point.
    pub fn interpolate_constraints<CS: ConstraintSystem<BaseField>>(
        &mut self,
        mut cs: CS,
        interpolation_point: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        let lagrange_coefficients = self.compute_lagrange_coefficients_constraints(
            cs.ns(|| "compute_lagrange_coefficients_constraints"),
            &interpolation_point,
        )?;

        let mut interpolation = NonNativeFieldVar::<TargetField, BaseField>::zero(cs.ns(|| "zero"))?;

        for (i, (lagrange_coefficient, polynomial_evaluation)) in lagrange_coefficients
            .iter()
            .zip(self.poly_evaluations.iter())
            .enumerate()
        {
            let intermediate = lagrange_coefficient.mul(
                cs.ns(|| format!("lagrange_coeff_mul_poly_evaluation_{}", i)),
                polynomial_evaluation,
            )?;

            interpolation = interpolation.add(
                cs.ns(|| format!("interpolation_plus_intermediate_{}", i)),
                &intermediate,
            )?;
        }
        Ok(interpolation)
    }
}
