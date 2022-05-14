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

use crate::{
    snark::marlin::{ahp::AHPError, fiat_shamir::FiatShamirError},
    SNARKError,
};

use core::fmt::Debug;

/// A `enum` specifying the possible failure modes of `Marlin`.
#[derive(Debug)]
pub enum MarlinError {
    /// The index is too large for the universal public parameters.
    IndexTooLarge(usize, usize),
    /// There was an error in the underlying holographic IOP.
    AHPError(AHPError),
    /// There was an error in Fiat-Shamir.
    FiatShamirError(FiatShamirError),
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

impl From<FiatShamirError> for MarlinError {
    fn from(err: FiatShamirError) -> Self {
        MarlinError::FiatShamirError(err)
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
            err => SNARKError::Crate("marlin", format!("{:?}", err)),
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
