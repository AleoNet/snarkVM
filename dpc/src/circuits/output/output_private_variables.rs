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

use crate::{Network, Record};
use snarkvm_algorithms::traits::EncryptionScheme;

use anyhow::Result;

#[derive(Clone)]
pub struct OutputPrivateVariables<N: Network> {
    // Outputs.
    pub(super) output_record: Record<N>,
    pub(super) encryption_randomness: <N::AccountEncryptionScheme as EncryptionScheme>::ScalarRandomness,

    pub(super) output_value_commitment_randomness: N::ProgramScalarField,
}

impl<N: Network> OutputPrivateVariables<N> {
    pub(crate) fn blank() -> Self {
        Self {
            output_record: Record::default(),
            encryption_randomness: Default::default(),
            output_value_commitment_randomness: Default::default(),
        }
    }

    pub(crate) fn new(
        output_record: Record<N>,
        encryption_randomness: <N::AccountEncryptionScheme as EncryptionScheme>::ScalarRandomness,
        output_value_commitment_randomness: N::ProgramScalarField,
    ) -> Result<Self> {
        Ok(Self { output_record, encryption_randomness, output_value_commitment_randomness })
    }
}
