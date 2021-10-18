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
use snarkvm_utilities::ToBytes;

use anyhow::Result;

#[derive(Clone, Debug)]
pub struct InnerPublicVariables<N: Network> {
    /// Transition ID
    transition_id: N::TransitionID,
    local_transitions_root: N::TransactionID,
    // These are required in natively verifying an inner circuit proof.
    // However for verification in the outer circuit, these must be provided as witness.
    /// Program ID
    pub(super) program_id: Option<N::ProgramID>,
}

impl<N: Network> InnerPublicVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            transition_id: Default::default(),
            local_transitions_root: Default::default(),
            program_id: Some(N::ProgramID::default()),
        }
    }

    pub(crate) fn new(
        transition_id: N::TransitionID,
        local_transitions_root: N::TransactionID,
        program_id: Option<N::ProgramID>,
    ) -> Self {
        Self {
            transition_id,
            local_transitions_root,
            program_id,
        }
    }

    /// Returns the transition ID.
    pub(crate) fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    pub(crate) fn local_transitions_root(&self) -> N::TransactionID {
        self.local_transitions_root
    }
}

impl<N: Network> ToConstraintField<N::InnerScalarField> for InnerPublicVariables<N> {
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        let mut v = Vec::new();

        if let Some(program_id) = &self.program_id {
            v.extend_from_slice(&program_id.to_bytes_le()?.to_field_elements()?);
        }

        v.extend_from_slice(&self.transition_id.to_field_elements()?);

        Ok(v)
    }
}
