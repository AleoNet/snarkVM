// Copyright (C) 2019-2022 Aleo Systems Inc.
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

#[derive(Copy, Clone, Debug, Default)]
pub struct ProgramPublicVariables<N: Network> {
    pub transition_id: N::TransitionID,
}

impl<N: Network> ProgramPublicVariables<N> {
    pub fn blank() -> Self {
        Self { transition_id: Default::default() }
    }

    pub fn new(transition_id: N::TransitionID) -> Self {
        Self { transition_id }
    }
}

/// Converts the public variables into bytes and packs them into field elements.
impl<N: Network> ToConstraintField<N::InnerScalarField> for ProgramPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = ToConstraintField::<N::InnerScalarField>::to_field_elements(&[0u8][..])?;
        v.extend_from_slice(&self.transition_id.to_field_elements()?);
        Ok(v)
    }
}
