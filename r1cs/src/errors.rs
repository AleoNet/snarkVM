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

pub type SynthesisResult<T> = Result<T, SynthesisError>;

/// This is an error that could occur during circuit synthesis contexts,
/// such as CRS generation, proving or verification.
#[derive(Debug, Error)]
pub enum SynthesisError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),
    /// During synthesis, we lacked knowledge of a variable assignment.
    #[error("An assignment for a variable could not be computed")]
    AssignmentMissing,
    /// Handles a failed conversion of objects into constraint field elements.
    #[error("Failed to convert object into constraint field elements")]
    ConstraintFieldError(#[from] snarkvm_fields::ConstraintFieldError),
    /// During synthesis, we divided by zero.
    #[error("Division by zero during synthesis")]
    DivisionByZero,
    /// During synthesis, we constructed an unsatisfiable constraint system.
    #[error("Unsatisfiable constraint system")]
    Unsatisfiable,
    /// During synthesis, our polynomials ended up being too high of degree
    #[error("Polynomial degree is too large")]
    PolynomialDegreeTooLarge,
    /// During proof generation, we encountered an identity in the CRS
    #[error("Encountered an identity element in the CRS")]
    UnexpectedIdentity,
    /// During proof generation, we encountered an I/O error with the CRS
    #[error("Encountered an I/O error")]
    IoError(std::io::Error),
    /// During verification, our verifying key was malformed.
    #[error("Malformed verifying key, public input count was {} but expected {}", _0, _1)]
    MalformedVerifyingKey(usize, usize),
    /// During CRS generation, we observed an unconstrained auxiliary variable
    #[error("Auxiliary variable was unconstrained")]
    UnconstrainedVariable,
}

impl From<std::io::Error> for SynthesisError {
    fn from(e: std::io::Error) -> SynthesisError {
        SynthesisError::IoError(e)
    }
}
