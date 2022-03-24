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

use snarkvm_fields::PrimeField;

use crate::polycommit::sonic_pc::{LabeledPolynomial, LabeledPolynomialWithBasis};

/// The first set of prover oracles.
#[derive(Debug, Clone)]
pub struct FirstOracles<'a, F: PrimeField> {
    /// The evaluations of `Az`.
    pub z_a: LabeledPolynomialWithBasis<'a, F>,
    /// The evaluations of `Bz`.
    pub z_b: LabeledPolynomialWithBasis<'a, F>,
    /// The sum-check hiding polynomial.
    pub mask_poly: Option<LabeledPolynomial<F>>,
    /// The LDE of `w`.
    pub w_poly: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub z_a_poly: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub z_b_poly: LabeledPolynomial<F>,
}

impl<'a, F: PrimeField> FirstOracles<'a, F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    pub fn iter_for_commit(&'a self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'a, F>> {
        [
            Some(&self.w_poly).map(Into::into),
            Some(self.z_a.clone()),
            Some(self.z_b.clone()),
            self.mask_poly.as_ref().map(Into::into),
        ]
        .into_iter()
        .flatten()
    }

    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when opening.
    pub fn iter_for_open(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [Some(&self.w_poly), Some(&self.z_a_poly), Some(&self.z_b_poly), self.mask_poly.as_ref()].into_iter().flatten()
    }
}

/// The second set of prover oracles.
#[derive(Debug)]
pub struct SecondOracles<F: PrimeField> {
    /// The polynomial `g` resulting from the first sumcheck.
    pub g_1: LabeledPolynomial<F>,
    /// The polynomial `h` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: PrimeField> SecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.g_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
#[derive(Debug)]
pub struct ThirdOracles<F: PrimeField> {
    /// The polynomial `g_a` resulting from the second sumcheck.
    pub g_a: LabeledPolynomial<F>,
    /// The polynomial `g_b` resulting from the second sumcheck.
    pub g_b: LabeledPolynomial<F>,
    /// The polynomial `g_c` resulting from the second sumcheck.
    pub g_c: LabeledPolynomial<F>,
}

impl<F: PrimeField> ThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.g_a, &self.g_b, &self.g_c].into_iter()
    }
}

#[derive(Debug)]
pub struct FourthOracles<F: PrimeField> {
    /// The polynomial `h_2` resulting from the second sumcheck.
    pub h_2: LabeledPolynomial<F>,
}

impl<F: PrimeField> FourthOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [&self.h_2].into_iter()
    }
}
