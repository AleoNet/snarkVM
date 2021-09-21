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

use crate::Network;
use snarkvm_fields::{ConstraintFieldError, ToConstraintField};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    Default(bound = "N: Network")
)]
pub struct PublicVariables<N: Network> {
    pub record_position: u8,
    pub local_data_root: N::LocalDataRoot,
}

impl<N: Network> PublicVariables<N> {
    pub fn new(record_position: u8, local_data_root: &N::LocalDataRoot) -> Self {
        Self {
            record_position,
            local_data_root: local_data_root.clone(),
        }
    }
}

/// Converts the public variables into bytes and packs them into field elements.
impl<N: Network> ToConstraintField<N::InnerScalarField> for PublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[self.record_position][..])?;
        v.extend_from_slice(&self.local_data_root.to_field_elements()?);
        Ok(v)
    }
}
