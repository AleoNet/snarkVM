use crate::{PhantomData, PrimeField, SynthesisError};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::fields::FieldVar;

pub struct AlgebraForAHP<F: PrimeField, CF: PrimeField> {
    field: PhantomData<F>,
    constraint_field: PhantomData<CF>,
}

impl<F: PrimeField, CF: PrimeField> AlgebraForAHP<F, CF> {
    #[tracing::instrument(target = "r1cs")]
    pub fn prepare(
        x: &NonNativeFieldVar<F, CF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        x.pow_by_constant(&[domain_size])
    }

    #[tracing::instrument(target = "r1cs")]
    pub fn prepared_eval_vanishing_polynomial(
        x_prepared: &NonNativeFieldVar<F, CF>,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        let one = NonNativeFieldVar::<F, CF>::one();
        let result = x_prepared - &one;
        Ok(result)
    }

    #[tracing::instrument(target = "r1cs")]
    pub fn eval_vanishing_polynomial(
        x: &NonNativeFieldVar<F, CF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        let x_prepared = Self::prepare(x, domain_size)?;
        Self::prepared_eval_vanishing_polynomial(&x_prepared)
    }

    #[tracing::instrument(target = "r1cs")]
    pub fn prepared_eval_bivariable_vanishing_polynomial(
        x: &NonNativeFieldVar<F, CF>,
        y: &NonNativeFieldVar<F, CF>,
        x_prepared: &NonNativeFieldVar<F, CF>,
        y_prepared: &NonNativeFieldVar<F, CF>,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        let denominator = x - y;

        let numerator = x_prepared - y_prepared;
        let denominator_invert = denominator.inverse()?;

        let result = numerator * &denominator_invert;

        Ok(result)
    }

    #[tracing::instrument(target = "r1cs")]
    pub fn eval_bivariate_vanishing_polynomial(
        x: &NonNativeFieldVar<F, CF>,
        y: &NonNativeFieldVar<F, CF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
        let x_prepared = Self::prepare(x, domain_size)?;
        let y_prepared = Self::prepare(y, domain_size)?;

        Self::prepared_eval_bivariable_vanishing_polynomial(x, y, &x_prepared, &y_prepared)
    }
}
