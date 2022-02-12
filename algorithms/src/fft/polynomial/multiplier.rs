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

/// A struct that helps multiply a batch of polynomials

use super::*;
use snarkvm_utilities::{cfg_into_iter, cfg_iter_mut};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub struct PolyMultiplier<'a, F: PrimeField> {
    polynomials: Vec<Cow<'a, DensePolynomial<F>>>,
    evaluations: Vec<Cow<'a, crate::fft::Evaluations<F>>>,
}

impl<'a, F: PrimeField> PolyMultiplier<'a, F> {
    pub fn new() -> Self {
        Self {
            polynomials: Vec::new(),
            evaluations: Vec::new(),
        }
    }

    pub fn add_polynomial(&mut self, poly: DensePolynomial<F>) {
        self.polynomials.push(Cow::Owned(poly))
    }

    pub fn add_evaluation(&mut self, evals: Evaluations<F>) {
        self.evaluations.push(Cow::Owned(evals))
    }

    pub fn add_polynomial_ref(&mut self, poly: &'a DensePolynomial<F>) {
        self.polynomials.push(Cow::Borrowed(poly))
    }

    pub fn add_evaluation_ref(&mut self, evals: &'a Evaluations<F>) {
        self.evaluations.push(Cow::Borrowed(evals))
    }

    /// Multiplies all polynomials stored in `self`.
    /// 
    /// Returns `None` if any of the stored evaluations are over a domain that's
    /// insufficiently large to interpolate the product, or if `F` does not contain
    /// a sufficiently large subgroup for interpolation.
    pub fn multiply(self) -> Option<DensePolynomial<F>> {
        if self.polynomials.is_empty() && self.evaluations.is_empty() {
            Some(DensePolynomial::zero())
        } else {
            let degree = self.polynomials.iter().map(|p| dbg!(p.degree() + 1)).sum::<usize>();
            let domain = EvaluationDomain::new(degree)?;
            if !self.evaluations.iter().all(|e| e.domain() == domain) {
                return None
            } else {
                let p = cfg_into_iter!(self.polynomials).map(|p| {
                    let mut p = p.to_owned().into_owned().coeffs;
                    p.resize(domain.size(), F::zero());
                    domain.fft_in_place_with_out_order(&mut p);
                    p
                });
                let e = cfg_into_iter!(self.evaluations).map(|e| {
                    let mut e = e.to_owned().into_owned().evaluations;
                    e.resize(domain.size(), F::zero());
                    crate::fft::domain::derange(&mut e);
                    e
                });
                #[cfg(feature = "parallel")]
                let mut result = p.chain(e).reduce_with(|mut a, b| {
                    cfg_iter_mut!(a).zip(b).for_each(|(a, b)| *a *= b);
                    a
                }).unwrap();
                #[cfg(not(feature = "parallel"))]
                let mut result = p.chain(e).reduce(|mut a, b| {
                    cfg_iter_mut!(a).zip(b).for_each(|(a, b)| *a *= b);
                    a
                }).unwrap();
                domain.out_order_ifft_in_place(&mut result);
                dbg!(degree);
                dbg!(domain.size());
                dbg!(result.len());
                Some(DensePolynomial::from_coefficients_vec(result))
            }
        }
        
    }
}
