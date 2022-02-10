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

use super::PolynomialLabel;
use crate::fft::{DensePolynomial, Evaluations as EvaluationsOnDomain};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_utilities::{cfg_iter, cfg_iter_mut, CanonicalDeserialize, CanonicalSerialize};
use std::{borrow::Cow, sync::Arc};

/// A polynomial along with information about its degree bound (if any), and the
/// maximum number of queries that will be made to it. This latter number determines
/// the amount of protection that will be provided to a commitment for this polynomial.
#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct LabeledPolynomial<F: Field> {
    label: PolynomialLabel,
    polynomial: Arc<DensePolynomial<F>>,
    degree_bound: Option<usize>,
    hiding_bound: Option<usize>,
}

impl<F: Field> core::ops::Deref for LabeledPolynomial<F> {
    type Target = DensePolynomial<F>;

    fn deref(&self) -> &Self::Target {
        &self.polynomial
    }
}

impl<F: Field> LabeledPolynomial<F> {
    /// Construct a new labeled polynomial by consuming `polynomial`.
    pub fn new(
        label: PolynomialLabel,
        polynomial: DensePolynomial<F>,
        degree_bound: Option<usize>,
        hiding_bound: Option<usize>,
    ) -> Self {
        Self { label, polynomial: Arc::new(polynomial), degree_bound, hiding_bound }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    /// Retrieve the polynomial from `self`.
    pub fn polynomial(&self) -> &DensePolynomial<F> {
        &self.polynomial
    }

    /// Evaluate the polynomial in `self`.
    pub fn evaluate(&self, point: F) -> F {
        self.polynomial.evaluate(point)
    }

    /// Retrieve the degree bound in `self`.
    pub fn degree_bound(&self) -> Option<usize> {
        self.degree_bound
    }

    /// Retrieve whether the polynomial in `self` should be hidden.
    pub fn is_hiding(&self) -> bool {
        self.hiding_bound.is_some()
    }

    /// Retrieve the hiding bound for the polynomial in `self`.
    pub fn hiding_bound(&self) -> Option<usize> {
        self.hiding_bound
    }
}

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone)]
pub struct LabeledPolynomialWithBasis<'a, F: PrimeField> {
    label: PolynomialLabel,
    pub polynomial: PolynomialWithBasis<'a, F>,
    hiding_bound: Option<usize>,
}

impl<'a, F: PrimeField> LabeledPolynomialWithBasis<'a, F> {
    /// Construct a new labeled polynomial by consuming `polynomial`.
    pub fn new_monomial_basis(
        label: PolynomialLabel,
        polynomial: &'a DensePolynomial<F>,
        degree_bound: Option<usize>,
        hiding_bound: Option<usize>,
    ) -> Self {
        let polynomial = PolynomialWithBasis::new_monomial_basis(polynomial, degree_bound);
        Self { label, polynomial, hiding_bound }
    }

    pub fn new_lagrange_basis(
        label: PolynomialLabel,
        polynomial: EvaluationsOnDomain<F>,
        hiding_bound: Option<usize>,
    ) -> Self {
        let polynomial = PolynomialWithBasis::new_lagrange_basis(polynomial);
        Self { label, polynomial, hiding_bound }
    }

    pub fn new_lagrange_basis_ref(
        label: PolynomialLabel,
        polynomial: &'a EvaluationsOnDomain<F>,
        hiding_bound: Option<usize>,
    ) -> Self {
        let polynomial = PolynomialWithBasis::new_lagrange_basis_ref(polynomial);
        Self { label, polynomial, hiding_bound }
    }

    /// Return the label for `self`.
    pub fn label(&self) -> &String {
        &self.label
    }

    pub fn degree(&self) -> usize {
        match &self.polynomial {
            PolynomialWithBasis::Lagrange { evaluations } => evaluations.evaluations.len(),
            PolynomialWithBasis::Monomial { polynomial, .. } => polynomial.degree(),
        }
    }

    /// Evaluate the polynomial in `self`.
    pub fn evaluate(&self, point: F) -> F {
        self.polynomial.evaluate(point)
    }

    /// Retrieve the degree bound in `self`.
    pub fn degree_bound(&self) -> Option<usize> {
        match self.polynomial {
            PolynomialWithBasis::Monomial { degree_bound, .. } => degree_bound,
            _ => None,
        }
    }

    /// Retrieve whether the polynomial in `self` should be hidden.
    pub fn is_hiding(&self) -> bool {
        self.hiding_bound.is_some()
    }

    /// Retrieve the hiding bound for the polynomial in `self`.
    pub fn hiding_bound(&self) -> Option<usize> {
        self.hiding_bound
    }
}

impl<'a, F: PrimeField> From<&'a LabeledPolynomial<F>> for LabeledPolynomialWithBasis<'a, F> {
    fn from(other: &'a LabeledPolynomial<F>) -> Self {
        let polynomial = PolynomialWithBasis::Monomial {
            polynomial: Cow::Borrowed(other.polynomial()),
            degree_bound: other.degree_bound(),
        };

        Self { label: other.label().clone(), polynomial, hiding_bound: other.hiding_bound }
    }
}

#[derive(Debug, Clone)]
pub enum PolynomialWithBasis<'a, F: PrimeField> {
    /// A polynomial in monomial basis, along with information about
    /// its degree bound (if any).
    Monomial { polynomial: Cow<'a, DensePolynomial<F>>, degree_bound: Option<usize> },

    /// A polynomial in Lagrange basis, along with information about
    /// its degree bound (if any).
    Lagrange { evaluations: Cow<'a, EvaluationsOnDomain<F>> },
}

impl<'a, F: PrimeField> PolynomialWithBasis<'a, F> {
    pub fn new_monomial_basis(polynomial: &'a DensePolynomial<F>, degree_bound: Option<usize>) -> Self {
        Self::Monomial { polynomial: Cow::Borrowed(polynomial), degree_bound }
    }

    pub fn new_lagrange_basis(evaluations: EvaluationsOnDomain<F>) -> Self {
        Self::Lagrange { evaluations: Cow::Owned(evaluations) }
    }

    pub fn new_lagrange_basis_ref(evaluations: &'a EvaluationsOnDomain<F>) -> Self {
        Self::Lagrange { evaluations: Cow::Borrowed(evaluations) }
    }

    pub fn evaluate(&self, point: F) -> F {
        match self {
            Self::Monomial { polynomial, .. } => polynomial.evaluate(point),
            Self::Lagrange { evaluations } => {
                let domain = evaluations.domain();
                let degree = domain.size() as u64;
                let multiplier = (point.pow(&[degree]) - F::one()) / F::from(degree);
                let powers: Vec<_> = domain.elements().collect();
                let mut denominators = cfg_iter!(powers).map(|pow| point - pow).collect::<Vec<_>>();
                snarkvm_fields::batch_inversion(&mut denominators);
                cfg_iter_mut!(denominators)
                    .zip(powers)
                    .zip(&evaluations.evaluations)
                    .map(|((denom, power), coeff)| *denom * power * coeff)
                    .sum::<F>()
                    * multiplier
            }
        }
    }
}
