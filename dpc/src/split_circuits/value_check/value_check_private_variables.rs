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

use anyhow::Result;

#[derive(Clone)]
pub struct ValueCheckPrivateVariables<N: Network> {
    /// The transition id.
    pub(super) transition_id: N::TransitionID,
    /// The commitments on the input record values.
    pub(super) input_value_commitments: Vec<N::ValueCommitment>,
    /// The commitments on the output record values.
    pub(super) output_value_commitments: Vec<N::ValueCommitment>,
}

impl<N: Network> ValueCheckPrivateVariables<N> {
    pub(crate) fn blank() -> Self {
        // TODO (raychu86): Handle different number of value commitments?
        let default_value_commitment: N::ProgramAffineCurve = Default::default();
        Self {
            transition_id: N::TransitionID::default(),
            input_value_commitments: vec![default_value_commitment.into(); N::NUM_INPUT_RECORDS],
            output_value_commitments: vec![default_value_commitment.into(); N::NUM_OUTPUT_RECORDS],
        }
    }

    pub(crate) fn new(
        transition_id: N::TransitionID,
        input_value_commitments: Vec<N::ValueCommitment>,
        output_value_commitments: Vec<N::ValueCommitment>,
    ) -> Result<Self> {
        Ok(Self { transition_id, input_value_commitments, output_value_commitments })
    }
}
