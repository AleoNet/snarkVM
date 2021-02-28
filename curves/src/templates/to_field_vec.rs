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

use crate::templates::short_weierstrass::short_weierstrass_jacobian::GroupAffine as SWAffine;
use crate::templates::short_weierstrass::short_weierstrass_jacobian::GroupProjective as SWProjective;
use crate::templates::twisted_edwards_extended::GroupAffine as TEAffine;
use crate::templates::twisted_edwards_extended::GroupProjective as TEProjective;
use crate::traits::ProjectiveCurve;
use crate::traits::SWModelParameters;
use crate::traits::TEModelParameters;
use snarkvm_fields::errors::ConstraintFieldError;
use snarkvm_fields::Field;
use snarkvm_fields::Fp2;
use snarkvm_fields::Fp2Parameters;
use snarkvm_fields::FpParameters;
use snarkvm_fields::PrimeField;
use snarkvm_fields::ToConstraintField;

impl<M: TEModelParameters, F: Field> ToConstraintField<F> for TEAffine<M>
where
    M::BaseField: ToConstraintField<F>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: TEModelParameters, F: Field> ToConstraintField<F> for TEProjective<M>
where
    M::BaseField: ToConstraintField<F>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        let affine = self.into_affine();
        let mut x_fe = affine.x.to_field_elements()?;
        let y_fe = affine.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: SWModelParameters, F: Field> ToConstraintField<F> for SWAffine<M>
where
    M::BaseField: ToConstraintField<F>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        let mut x_fe = self.x.to_field_elements()?;
        let y_fe = self.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}

impl<M: SWModelParameters, F: Field> ToConstraintField<F> for SWProjective<M>
where
    M::BaseField: ToConstraintField<F>,
{
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        let affine = self.into_affine();
        let mut x_fe = affine.x.to_field_elements()?;
        let y_fe = affine.y.to_field_elements()?;
        x_fe.extend_from_slice(&y_fe);
        Ok(x_fe)
    }
}
