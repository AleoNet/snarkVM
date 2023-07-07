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

/// The error type for `PolynomialCommitment`.
#[derive(Debug)]
pub enum PCError {
    AnyhowError(anyhow::Error),

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
        /// Maximum degree.
        max_degree: usize,
        /// Index of the offending polynomial.
        label: String,
    },

    Terminated,
}

impl snarkvm_utilities::error::Error for PCError {}

impl From<anyhow::Error> for PCError {
    fn from(other: anyhow::Error) -> Self {
        Self::AnyhowError(other)
    }
}

impl core::fmt::Display for PCError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AnyhowError(error) => write!(f, "{error}"),
            Self::MissingPolynomial { label } => {
                write!(f, "`QuerySet` refers to polynomial \"{label}\", but it was not provided.")
            }
            Self::MissingEvaluation { label } => write!(
                f,
                "`QuerySet` refers to polynomial \"{label}\", but `Evaluations` does not contain an evaluation for it."
            ),
            Self::MissingRng => write!(f, "hiding commitments require `Some(rng)`"),
            Self::DegreeIsZero => write!(f, "this scheme does not support committing to degree 0 polynomials"),
            Self::TooManyCoefficients { num_coefficients, num_powers } => write!(
                f,
                "the number of coefficients in the polynomial ({num_coefficients:?}) is greater than\
                 the maximum number of powers in `Powers` ({num_powers:?})"
            ),
            Self::HidingBoundIsZero => write!(f, "this scheme does not support non-`None` hiding bounds that are 0"),
            Self::HidingBoundToolarge { hiding_poly_degree, num_powers } => write!(
                f,
                "the degree of the hiding poly ({hiding_poly_degree:?}) is not less than the maximum number of powers in `Powers` ({num_powers:?})"
            ),
            Self::TrimmingDegreeTooLarge => write!(f, "the degree provided to `trim` was too large"),
            Self::EquationHasDegreeBounds(e) => {
                write!(f, "the eqaution \"{e}\" contained degree-bounded polynomials")
            }
            Self::UnsupportedDegreeBound(bound) => {
                write!(f, "the degree bound ({bound:?}) is not supported by the parameters")
            }
            Self::LagrangeBasisSizeIsNotPowerOfTwo => {
                write!(f, "the Lagrange Basis size is not a power of two")
            }
            Self::UnsupportedLagrangeBasisSize(size) => {
                write!(f, "the Lagrange basis size ({size:?}) is not supported by the parameters")
            }
            Self::LagrangeBasisSizeIsTooLarge => {
                write!(f, "the Lagrange Basis size larger than max supported degree")
            }
            Self::IncorrectDegreeBound { poly_degree, degree_bound, max_degree, label } => write!(
                f,
                "the degree bound ({degree_bound}) for the polynomial {label} \
                 (having degree {poly_degree}) is greater than the maximum degree ({max_degree})"
            ),
            Self::Terminated => write!(f, "terminated"),
        }
    }
}
