use crate::{constraints::polynomial::AlgebraForAHP, PrimeField, SynthesisError, Vec};
use ark_ff::{batch_inversion, Field};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::FieldVar, R1CSVar};

pub struct LagrangeInterpolator<F: PrimeField> {
    all_domain_elems: Vec<F>,
    v_inv_elems: Vec<F>,
    domain_vp: VanishingPolynomial<F>,
    poly_evaluations: Vec<F>,
}

pub struct LagrangeInterpolationVar<F: PrimeField, CF: PrimeField> {
    pub lagrange_interpolator: LagrangeInterpolator<F>,
    pub vp_t: Option<NonNativeFieldVar<F, CF>>,
    poly_evaluations: Vec<NonNativeFieldVar<F, CF>>,
}

pub struct VanishingPolynomial<F: Field> {
    constant_term: F,
    order_h: u64,
}

impl<F: Field> VanishingPolynomial<F> {
    pub fn new(offset: F, order_h: u64) -> Self {
        VanishingPolynomial {
            constant_term: offset.pow([order_h]),
            order_h,
        }
    }

    pub fn evaluate(&self, x: &F) -> F {
        let mut result = x.pow([self.order_h]);
        result -= &self.constant_term;
        result
    }
}

impl<CF: PrimeField> LagrangeInterpolator<CF> {
    pub fn new(domain_generator: CF, domain_order: u64, poly_evaluations: Vec<CF>) -> Self {
        let domain_order = domain_order;
        let poly_evaluations_size = poly_evaluations.len();

        let mut cur_elem = domain_generator;
        let mut all_domain_elems = vec![CF::one()];
        let mut v_inv_elems: Vec<CF> = Vec::new();

        for _ in 1..poly_evaluations_size {
            all_domain_elems.push(cur_elem);
            cur_elem *= domain_generator;
        }

        let g_inv = domain_generator.inverse().unwrap();
        let m = CF::from(domain_order as u128);
        let mut v_inv_i = m;
        for _ in 0..poly_evaluations_size {
            v_inv_elems.push(v_inv_i);
            v_inv_i *= g_inv;
        }

        let vp = VanishingPolynomial::new(domain_generator, domain_order);

        let lagrange_interpolation: LagrangeInterpolator<CF> = LagrangeInterpolator {
            all_domain_elems,
            v_inv_elems,
            domain_vp: vp,
            poly_evaluations,
        };
        lagrange_interpolation
    }

    fn compute_lagrange_coefficients(&self, interpolation_point: CF) -> Vec<CF> {
        let poly_evaluations_size = self.poly_evaluations.len();

        let vp_t_inv = self
            .domain_vp
            .evaluate(&interpolation_point)
            .inverse()
            .unwrap();
        let mut inverted_lagrange_coeffs: Vec<CF> = Vec::with_capacity(self.all_domain_elems.len());
        for i in 0..poly_evaluations_size {
            let l = vp_t_inv * self.v_inv_elems[i];
            let r = self.all_domain_elems[i];
            inverted_lagrange_coeffs.push(l * (interpolation_point - r));
        }
        let lagrange_coeffs = inverted_lagrange_coeffs.as_mut_slice();
        batch_inversion::<CF>(lagrange_coeffs);

        lagrange_coeffs.to_vec()
    }

    pub fn interpolate(&self, interpolation_point: CF) -> CF {
        let poly_evaluations_size = self.poly_evaluations.len();

        let lagrange_coeffs = self.compute_lagrange_coefficients(interpolation_point);
        let mut interpolation = CF::zero();

        for (lagrange_coeff, poly_evaluation) in lagrange_coeffs
            .iter()
            .zip(self.poly_evaluations.iter())
            .take(poly_evaluations_size)
        {
            interpolation += *lagrange_coeff * poly_evaluation;
        }
        interpolation
    }
}

impl<F: PrimeField, CF: PrimeField> LagrangeInterpolationVar<F, CF> {
    #[tracing::instrument(target = "r1cs")]
    pub fn new(
        domain_generator: F,
        domain_dim: u64,
        poly_evaluations: &[NonNativeFieldVar<F, CF>],
    ) -> Self {
        let poly_evaluations_size = poly_evaluations.len();

        let mut poly_evaluations_cf: Vec<F> = Vec::new();
        for poly_evaluation in poly_evaluations.iter().take(poly_evaluations_size) {
            poly_evaluations_cf.push(poly_evaluation.value().unwrap_or_default());
        }

        let lagrange_interpolator: LagrangeInterpolator<F> =
            LagrangeInterpolator::new(domain_generator, domain_dim, poly_evaluations_cf);

        LagrangeInterpolationVar {
            lagrange_interpolator,
            vp_t: None,
            poly_evaluations: (*poly_evaluations).to_vec(),
        }
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn compute_lagrange_coefficients_constraints(
        &mut self,
        interpolation_point: &NonNativeFieldVar<F, CF>,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
        let cs = interpolation_point.cs();

        let poly_evaluations_size = self.poly_evaluations.len();

        let t = interpolation_point.clone();
        let lagrange_coeffs = self
            .lagrange_interpolator
            .compute_lagrange_coefficients(t.value().unwrap_or_default());
        let mut lagrange_coeffs_fg: Vec<NonNativeFieldVar<F, CF>> = Vec::new();

        let vp_t = if self.vp_t.is_some() {
            self.vp_t.clone().unwrap()
        } else {
            AlgebraForAHP::<F, CF>::eval_vanishing_polynomial(
                &t,
                self.lagrange_interpolator.domain_vp.order_h,
            )?
        };

        if self.vp_t.is_none() {
            self.vp_t = Some(vp_t.clone());
        }

        for ((all_domain_elem, v_inv_elem), lagrange_coeff) in self
            .lagrange_interpolator
            .all_domain_elems
            .iter()
            .zip(self.lagrange_interpolator.v_inv_elems.iter())
            .zip(lagrange_coeffs.iter())
            .take(poly_evaluations_size)
        {
            let add_constant_val: F = -*all_domain_elem;

            let lag_coeff = NonNativeFieldVar::<F, CF>::new_witness(
                ark_relations::ns!(cs, "generate lagrange coefficient"),
                || Ok(*lagrange_coeff),
            )?;
            lagrange_coeffs_fg.push(lag_coeff.clone());

            let test_elem = (&t + add_constant_val) * *v_inv_elem * &lag_coeff;
            test_elem.enforce_equal(&vp_t)?;
        }
        Ok(lagrange_coeffs_fg)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn interpolate_constraints(
        &mut self,
        interpolation_point: &NonNativeFieldVar<F, CF>,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        let lagrange_coeffs =
            self.compute_lagrange_coefficients_constraints(&interpolation_point)?;

        let mut interpolation = NonNativeFieldVar::<F, CF>::zero();

        for (lagrange_coeff, poly_evaluation) in
            lagrange_coeffs.iter().zip(self.poly_evaluations.iter())
        {
            let intermediate = lagrange_coeff * poly_evaluation;
            interpolation += &intermediate;
        }
        Ok(interpolation)
    }
}
