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

use snarkvm_algorithms::errors::SNARKError;
use snarkvm_fields::ConstraintFieldError;
use snarkvm_parameters::errors::ParameterError;

use std::io::Error as IoError;
use thiserror::Error;

/// An error when generating/verifying a Proof of Succinct Work
#[derive(Debug, Error)]
pub enum PoswError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),

    /// Thrown if the mask conversion to a field element fails
    #[error(transparent)]
    ConstraintFieldError(#[from] ConstraintFieldError),

    /// Thrown when there's an IO error
    #[error(transparent)]
    IoError(#[from] IoError),

    /// Thrown when the parameters cannot be loaded
    #[error("could not load PoSW parameters: {0}")]
    Parameters(#[from] ParameterError),

    /// Thrown when a proof fails verification
    #[error("could not verify PoSW")]
    PoswVerificationFailed,

    /// Thrown when there's an internal error in the underlying SNARK
    #[error(transparent)]
    SnarkError(#[from] SNARKError),
}

impl From<PoswError> for std::io::Error {
    fn from(error: PoswError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", error))
    }
}
