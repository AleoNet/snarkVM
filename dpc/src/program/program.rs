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

use crate::Parameters;
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};

/// Program index, path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct Execution<C: Parameters> {
    pub program_path: MerklePath<C::ProgramCircuitTreeParameters>,
    pub verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey,
    pub proof: <C::ProgramSNARK as SNARK>::Proof,
}

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    Debug(bound = "C: Parameters"),
    Default(bound = "C: Parameters")
)]
pub struct ProgramPublicVariables<C: Parameters> {
    pub local_data_root: C::LocalDataRoot,
    pub record_position: u8,
}

impl<C: Parameters> ProgramPublicVariables<C> {
    pub fn new(local_data_root: &C::LocalDataRoot, record_position: u8) -> Self {
        Self {
            local_data_root: local_data_root.clone(),
            record_position,
        }
    }
}

/// Converts the program public variables into bytes and packs them into field elements.
impl<C: Parameters> ToConstraintField<C::InnerScalarField> for ProgramPublicVariables<C> {
    fn to_field_elements(&self) -> Result<Vec<C::InnerScalarField>, ConstraintFieldError> {
        let mut v = ToConstraintField::<C::InnerScalarField>::to_field_elements(&[self.record_position][..])?;
        v.extend_from_slice(&self.local_data_root.to_field_elements()?);
        Ok(v)
    }
}
