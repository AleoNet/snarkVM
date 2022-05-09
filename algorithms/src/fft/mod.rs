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

//! This crate implements functions for manipulating polynomials over finite fields,
//! including FFTs.

pub mod domain;
pub use domain::EvaluationDomain;

pub mod evaluations;
pub use evaluations::Evaluations;

pub mod polynomial;
pub use polynomial::{DensePolynomial, Polynomial, SparsePolynomial};

#[cfg(test)]
mod tests;

use snarkvm_fields::FftField;

/// Types that can be FFT-ed must implement this trait.
pub trait DomainCoeff<F: FftField>:
    Copy
    + Send
    + Sync
    + core::ops::Add<Output = Self>
    + core::ops::Sub<Output = Self>
    + core::ops::AddAssign
    + core::ops::SubAssign
    + snarkvm_fields::Zero
    + core::ops::MulAssign<F>
{
}

impl<T, F> DomainCoeff<F> for T
where
    F: FftField,
    T: Copy
        + Send
        + Sync
        + snarkvm_fields::Zero
        + core::ops::AddAssign
        + core::ops::SubAssign
        + core::ops::MulAssign<F>
        + core::ops::Add<Output = Self>
        + core::ops::Sub<Output = Self>,
{
}
