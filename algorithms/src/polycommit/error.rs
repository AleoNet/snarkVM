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

use crate::snark::marlin::FiatShamirError;

/// The error type for `PolynomialCommitment`.
#[derive(Debug)]
pub enum PCError {
    FSError(FiatShamirError),
    /// The query set contains a label for a polynomial that was not provided as
    /// input to the `PC::open`.
    MissingPolynomial {
        /// The label of the missing polynomial.
        label: String,
    },

    /// `Evaluations` does not contain an evaluation for the polynomial labelled
    /// `label` at a particular query.
    MissingEvaluation {
        /// The label of the missing polynomial.
        label: String,
    },

    /// The provided polynomial was meant to be hiding, but `rng` was `None`.
    MissingRng,

    /// The degree provided in setup was too small; degree 0 polynomials
    /// are not supported.
    DegreeIsZero,

    /// The degree of the polynomial passed to `commit` or `open`
    /// was too large.
    TooManyCoefficients {
        /// The number of coefficients in the polynomial.
        num_coefficients: usize,
        /// The maximum number of powers provided in `Powers`.
        num_powers: usize,
    },

    /// The hiding bound was not `None`, but the hiding bound was zero.
    HidingBoundIsZero,

    /// The hiding bound was too large for the given `Powers`.
    HidingBoundToolarge {
        /// The hiding bound
        hiding_poly_degree: usize,
        /// The number of powers.
        num_powers: usize,
    },

    /// The lagrange basis is not a power of two.
    LagrangeBasisSizeIsNotPowerOfTwo,

    /// The lagrange basis is larger than the supported degree,
    LagrangeBasisSizeIsTooLarge,

    /// The degree provided to `trim` was too large.
    TrimmingDegreeTooLarge,

    /// The provided equation contained multiple polynomials, of which least one
    /// had a strict degree bound.
    EquationHasDegreeBounds(String),

    /// The required degree bound is not supported by ck/vk
    UnsupportedDegreeBound(usize),

    /// The provided equation contained multiple polynomials, of which least one
    /// had a strict degree bound.
    UnsupportedLagrangeBasisSize(usize),

    /// The degree bound for the `index`-th polynomial passed to `commit`, `open`
    /// or `check` was incorrect, that is, `degree_bound >= poly_degree` or
    /// `degree_bound <= max_degree`.
    IncorrectDegreeBound {
        /// Degree of the polynomial.
        poly_degree: usize,
        /// Degree bound.
        degree_bound: usize,
        /// Maximum supported degree.
        supported_degree: usize,
        /// Index of the offending polynomial.
        label: String,
    },

    Terminated,
}

impl snarkvm_utilities::error::Error for PCError {}

impl From<FiatShamirError> for PCError {
    fn from(other: FiatShamirError) -> Self {
        Self::FSError(other)
    }
}

impl core::fmt::Display for PCError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            PCError::FSError(e) => write!(f, "{e}"),
            PCError::MissingPolynomial { label } => {
                write!(f, "`QuerySet` refers to polynomial \"{}\", but it was not provided.", label)
            }
            PCError::MissingEvaluation { label } => write!(
                f,
                "`QuerySet` refers to polynomial \"{}\", but `Evaluations` does not contain an evaluation for it.",
                label
            ),
            PCError::MissingRng => write!(f, "hiding commitments require `Some(rng)`"),
            PCError::DegreeIsZero => write!(f, "this scheme does not support committing to degree 0 polynomials"),
            PCError::TooManyCoefficients { num_coefficients, num_powers } => write!(
                f,
                "the number of coefficients in the polynomial ({:?}) is greater than\
                 the maximum number of powers in `Powers` ({:?})",
                num_coefficients, num_powers
            ),
            PCError::HidingBoundIsZero => write!(f, "this scheme does not support non-`None` hiding bounds that are 0"),
            PCError::HidingBoundToolarge { hiding_poly_degree, num_powers } => write!(
                f,
                "the degree of the hiding poly ({:?}) is not less than the maximum number of powers in `Powers` ({:?})",
                hiding_poly_degree, num_powers
            ),
            PCError::TrimmingDegreeTooLarge => write!(f, "the degree provided to `trim` was too large"),
            PCError::EquationHasDegreeBounds(e) => {
                write!(f, "the eqaution \"{}\" contained degree-bounded polynomials", e)
            }
            PCError::UnsupportedDegreeBound(bound) => {
                write!(f, "the degree bound ({:?}) is not supported by the parameters", bound)
            }
            PCError::LagrangeBasisSizeIsNotPowerOfTwo => {
                write!(f, "the Lagrange Basis size is not a power of two")
            }
            PCError::UnsupportedLagrangeBasisSize(size) => {
                write!(f, "the Lagrange basis size ({:?}) is not supported by the parameters", size)
            }
            PCError::LagrangeBasisSizeIsTooLarge => {
                write!(f, "the Lagrange Basis size larger than max supported degree")
            }
            PCError::IncorrectDegreeBound { poly_degree, degree_bound, supported_degree, label } => write!(
                f,
                "the degree bound ({:?}) for the polynomial {} \
                 (having degree {:?}) is greater than the maximum \
                 supported degree ({:?})",
                degree_bound, label, poly_degree, supported_degree
            ),
            PCError::Terminated => write!(f, "terminated"),
        }
    }
}
