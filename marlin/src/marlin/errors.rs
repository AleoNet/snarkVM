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

use snarkvm_algorithms::SNARKError;

use std::fmt::Debug;

/// A `enum` specifying the possible failure modes of `Marlin`.
#[derive(Debug)]
pub enum MarlinError {
    /// The index is too large for the universal public parameters.
    IndexTooLarge(usize, usize),
    /// There was an error in the underlying holographic IOP.
    AHPError(crate::ahp::AHPError),
    /// There was an error in Fiat-Shamir.
    FiatShamirError(crate::fiat_shamir::FiatShamirError),
    /// There was a synthesis error.
    R1CSError(snarkvm_r1cs::SynthesisError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(snarkvm_polycommit::Error),
    Terminated,
}

impl From<crate::ahp::AHPError> for MarlinError {
    fn from(err: crate::ahp::AHPError) -> Self {
        MarlinError::AHPError(err)
    }
}

impl From<crate::fiat_shamir::FiatShamirError> for MarlinError {
    fn from(err: crate::fiat_shamir::FiatShamirError) -> Self {
        MarlinError::FiatShamirError(err)
    }
}

impl From<snarkvm_r1cs::SynthesisError> for MarlinError {
    fn from(err: snarkvm_r1cs::SynthesisError) -> Self {
        MarlinError::R1CSError(err)
    }
}

impl From<snarkvm_polycommit::Error> for MarlinError {
    fn from(err: snarkvm_polycommit::Error) -> Self {
        match err {
            snarkvm_polycommit::Error::Terminated => MarlinError::Terminated,
            err => MarlinError::PolynomialCommitmentError(err),
        }
    }
}

impl MarlinError {
    pub fn into_snark_error(&self, prefix: &str) -> SNARKError {
        match self {
            MarlinError::Terminated => SNARKError::Terminated,
            err => SNARKError::Crate("marlin", format!("{} - {:?}", prefix, err)),
        }
    }
}

impl From<MarlinError> for SNARKError {
    fn from(error: MarlinError) -> Self {
        match error {
            MarlinError::Terminated => SNARKError::Terminated,
            err => SNARKError::Crate("marlin", format!("{:?}", err)),
        }
    }
}
