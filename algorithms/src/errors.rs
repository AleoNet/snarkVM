// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use snarkvm_fields::ConstraintFieldError;
use snarkvm_r1cs::SynthesisError;

#[derive(Debug, Error)]
pub enum SNARKError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    #[error("{}", _0)]
    ConstraintFieldError(#[from] ConstraintFieldError),

    #[error("{}: {}", _0, _1)]
    Crate(&'static str, String),

    #[error("Expected a circuit-specific SRS in SNARK")]
    ExpectedCircuitSpecificSRS,

    #[error("{}", _0)]
    Message(String),

    #[error("{}", _0)]
    SynthesisError(SynthesisError),

    #[error("Batch size was zero; must be at least 1")]
    EmptyBatch,

    #[error("Batch size was different between public input and proof")]
    BatchSizeMismatch,

    #[error("Circuit not found")]
    CircuitNotFound,

    #[error("terminated")]
    Terminated,
}

impl From<SynthesisError> for SNARKError {
    fn from(error: SynthesisError) -> Self {
        SNARKError::SynthesisError(error)
    }
}
