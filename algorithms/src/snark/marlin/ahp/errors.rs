// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum AHPError {
    /// Anyhow error
    Anyhow(anyhow::Error),
    /// The batch size is zero.
    BatchSizeIsZero,
    /// An error occurred during constraint generation.
    ConstraintSystemError(crate::r1cs::errors::SynthesisError),
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// During verification, a required evaluation is missing
    MissingEval(String),
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
    /// During synthesis, our polynomials ended up being too high of degree
    PolynomialDegreeTooLarge,
}

impl From<crate::r1cs::errors::SynthesisError> for AHPError {
    fn from(other: crate::r1cs::errors::SynthesisError) -> Self {
        AHPError::ConstraintSystemError(other)
    }
}

impl From<anyhow::Error> for AHPError {
    fn from(other: anyhow::Error) -> Self {
        AHPError::Anyhow(other)
    }
}
