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

use crate::{ahp::AHPError, marlin::MarlinError};

use core::fmt::Display;
use std::fmt::{Debug, Formatter};

/// Error handling for Marlin constraints.
pub struct MarlinConstraintsError {
    /// Error message.
    pub error_msg: String,
}

impl<E> From<MarlinError<E>> for MarlinConstraintsError
where
    E: std::error::Error,
{
    fn from(e: MarlinError<E>) -> Self {
        match e {
            MarlinError::<E>::IndexTooLarge(u, v) => Self {
                error_msg: format!("index of {} is too large, maximum degree of {}", v, u),
            },
            MarlinError::<E>::AHPError(err) => match err {
                AHPError::ConstraintSystemError(error) => Self {
                    error_msg: error.to_string(),
                },
                AHPError::FiatShamirError(error) => Self {
                    error_msg: error.to_string(),
                },
                AHPError::InvalidPublicInputLength => Self {
                    error_msg: String::from("invalid public input length"),
                },
                AHPError::InstanceDoesNotMatchIndex => Self {
                    error_msg: String::from("instance does not match index"),
                },
                AHPError::MissingEval(str) => Self {
                    error_msg: String::from("missing eval: ") + &*str,
                },
                AHPError::NonSquareMatrix => Self {
                    error_msg: String::from("non-sqaure matrix"),
                },
            },
            MarlinError::<E>::R1CSError(err) => Self {
                error_msg: err.to_string(),
            },
            MarlinError::<E>::FiatShamirError(err) => Self {
                error_msg: err.to_string(),
            },
            MarlinError::<E>::PolynomialCommitmentError(err) => Self {
                error_msg: err.to_string(),
            },
            MarlinError::Terminated => Self {
                error_msg: "terminated".to_string(),
            },
        }
    }
}

impl Debug for MarlinConstraintsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}

impl Display for MarlinConstraintsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}
