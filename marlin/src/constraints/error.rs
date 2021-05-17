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

use crate::marlin::MarlinError;

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
            crate::marlin::MarlinError::<E>::IndexTooLarge(u, v) => Self {
                error_msg: format!("index of {} is too large, maximum degree of {}", v, u),
            },
            crate::marlin::MarlinError::<E>::AHPError(err) => match err {
                crate::ahp::AHPError::ConstraintSystemError(error) => Self {
                    error_msg: error.to_string(),
                },
                crate::ahp::AHPError::FiatShamirError(error) => Self {
                    error_msg: error.to_string(),
                },
                crate::ahp::AHPError::InvalidPublicInputLength => Self {
                    error_msg: String::from("invalid public input length"),
                },
                crate::ahp::AHPError::InstanceDoesNotMatchIndex => Self {
                    error_msg: String::from("instance does not match index"),
                },
                crate::ahp::AHPError::MissingEval(str) => Self {
                    error_msg: String::from("missing eval: ") + &*str,
                },
                crate::ahp::AHPError::NonSquareMatrix => Self {
                    error_msg: String::from("non-sqaure matrix"),
                },
            },
            crate::marlin::MarlinError::<E>::R1CSError(err) => Self {
                error_msg: err.to_string(),
            },
            crate::marlin::MarlinError::<E>::FiatShamirError(err) => Self {
                error_msg: err.to_string(),
            },
            crate::marlin::MarlinError::<E>::PolynomialCommitmentError(err) => Self {
                error_msg: err.to_string(),
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
