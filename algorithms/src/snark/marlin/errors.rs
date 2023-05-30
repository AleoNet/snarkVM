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

use crate::{snark::marlin::ahp::AHPError, SNARKError};

use core::fmt::Debug;

/// A `enum` specifying the possible failure modes of `Marlin`.
#[derive(Debug)]
pub enum MarlinError {
    /// The index is too large for the universal public parameters.
    IndexTooLarge(usize, usize),
    /// There was an error in the underlying holographic IOP.
    AHPError(AHPError),
    /// There was a synthesis error.
    R1CSError(snarkvm_r1cs::SynthesisError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(crate::polycommit::PCError),
    Terminated,
}

impl From<AHPError> for MarlinError {
    fn from(err: AHPError) -> Self {
        MarlinError::AHPError(err)
    }
}

impl From<snarkvm_r1cs::SynthesisError> for MarlinError {
    fn from(err: snarkvm_r1cs::SynthesisError) -> Self {
        MarlinError::R1CSError(err)
    }
}

impl From<crate::polycommit::PCError> for MarlinError {
    fn from(err: crate::polycommit::PCError) -> Self {
        match err {
            crate::polycommit::PCError::Terminated => MarlinError::Terminated,
            err => MarlinError::PolynomialCommitmentError(err),
        }
    }
}

impl From<MarlinError> for SNARKError {
    fn from(error: MarlinError) -> Self {
        match error {
            MarlinError::Terminated => SNARKError::Terminated,
            err => SNARKError::Crate("marlin", format!("{err:?}")),
        }
    }
}

impl From<AHPError> for SNARKError {
    fn from(err: AHPError) -> Self {
        MarlinError::AHPError(err).into()
    }
}

impl From<crate::polycommit::PCError> for SNARKError {
    fn from(err: crate::polycommit::PCError) -> Self {
        match err {
            crate::polycommit::PCError::Terminated => MarlinError::Terminated,
            err => MarlinError::PolynomialCommitmentError(err),
        }
        .into()
    }
}
