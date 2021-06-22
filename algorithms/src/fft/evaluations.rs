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

//! A polynomial represented in evaluations form.

use crate::fft::{DensePolynomial, EvaluationDomain};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{errors::SerializationError, serialize::*};

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use crate::fft::domain::FftEvaluationDomain;

/// Stores a polynomial in evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Evaluations<F: PrimeField, D: EvaluationDomain<F> = FftEvaluationDomain<F>> {
    /// The evaluations of a polynomial over the domain `D`
    pub evaluations: Vec<F>,
    #[doc(hidden)]
    domain: D,
}

impl<F: PrimeField, D: EvaluationDomain<F>> Evaluations<F, D> {
    /// Construct `Self` from evaluations and a domain.
    pub fn from_vec_and_domain(evaluations: Vec<F>, domain: D) -> Self {
        Self { evaluations, domain }
    }

    /// Interpolate a polynomial from a list of evaluations
    pub fn interpolate_by_ref(&self) -> DensePolynomial<F> {
        DensePolynomial::from_coefficients_vec(self.domain.ifft(&self.evaluations))
    }

    /// Interpolate a polynomial from a list of evaluations
    pub fn interpolate(self) -> DensePolynomial<F> {
        let Self {
            evaluations: mut evals,
            domain,
        } = self;
        domain.ifft_in_place(&mut evals);
        DensePolynomial::from_coefficients_vec(evals)
    }
}

impl<F: PrimeField, D: EvaluationDomain<F>> std::ops::Index<usize> for Evaluations<F, D> {
    type Output = F;

    fn index(&self, index: usize) -> &F {
        &self.evaluations[index]
    }
}

impl<'a, 'b, F: PrimeField, D: EvaluationDomain<F>> Mul<&'a Evaluations<F, D>> for &'b Evaluations<F, D> {
    type Output = Evaluations<F, D>;

    #[inline]
    fn mul(self, other: &'a Evaluations<F, D>) -> Evaluations<F, D> {
        let mut result = self.clone();
        result *= other;
        result
    }
}

impl<'a, F: PrimeField, D: EvaluationDomain<F>> MulAssign<&'a Evaluations<F, D>> for Evaluations<F, D> {
    #[inline]
    fn mul_assign(&mut self, other: &'a Evaluations<F, D>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evaluations
            .iter_mut()
            .zip(&other.evaluations)
            .for_each(|(a, b)| *a *= b);
    }
}

impl<'a, 'b, F: PrimeField, D: EvaluationDomain<F>> Add<&'a Evaluations<F, D>> for &'b Evaluations<F, D> {
    type Output = Evaluations<F, D>;

    #[inline]
    fn add(self, other: &'a Evaluations<F, D>) -> Evaluations<F, D> {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl<'a, F: PrimeField, D: EvaluationDomain<F>> AddAssign<&'a Evaluations<F, D>> for Evaluations<F, D> {
    #[inline]
    fn add_assign(&mut self, other: &'a Evaluations<F, D>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evaluations
            .iter_mut()
            .zip(&other.evaluations)
            .for_each(|(a, b)| *a += b);
    }
}

impl<'a, 'b, F: PrimeField, D: EvaluationDomain<F>> Sub<&'a Evaluations<F, D>> for &'b Evaluations<F, D> {
    type Output = Evaluations<F, D>;

    #[inline]
    fn sub(self, other: &'a Evaluations<F, D>) -> Evaluations<F, D> {
        let mut result = self.clone();
        result -= other;
        result
    }
}

impl<'a, F: PrimeField, D: EvaluationDomain<F>> SubAssign<&'a Evaluations<F, D>> for Evaluations<F, D> {
    #[inline]
    fn sub_assign(&mut self, other: &'a Evaluations<F, D>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evaluations
            .iter_mut()
            .zip(&other.evaluations)
            .for_each(|(a, b)| *a -= b);
    }
}

impl<'a, 'b, F: PrimeField, D: EvaluationDomain<F>> Div<&'a Evaluations<F, D>> for &'b Evaluations<F, D> {
    type Output = Evaluations<F, D>;

    #[inline]
    fn div(self, other: &'a Evaluations<F, D>) -> Evaluations<F, D> {
        let mut result = self.clone();
        result /= other;
        result
    }
}

impl<'a, F: PrimeField, D: EvaluationDomain<F>> DivAssign<&'a Evaluations<F, D>> for Evaluations<F, D> {
    #[inline]
    fn div_assign(&mut self, other: &'a Evaluations<F, D>) {
        assert_eq!(self.domain, other.domain, "domains are unequal");
        self.evaluations
            .iter_mut()
            .zip(&other.evaluations)
            .for_each(|(a, b)| *a /= b);
    }
}
