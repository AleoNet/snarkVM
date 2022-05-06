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

use std::collections::BTreeMap;

use snarkvm_fields::PrimeField;

use crate::polycommit::sonic_pc::{LabeledPolynomial, LabeledPolynomialWithBasis, PolynomialInfo, PolynomialLabel};

/// The first set of prover oracles.
#[derive(Debug, Clone)]
pub struct FirstOracles<'a, F: PrimeField> {
    pub(in crate::snark::marlin) batches: Vec<SingleEntry<'a, F>>,
    /// The sum-check hiding polynomial.
    pub mask_poly: Option<LabeledPolynomial<F>>,
}

impl<'a, F: PrimeField> FirstOracles<'a, F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    #[allow(clippy::needless_collect)]
    pub fn iter_for_commit(&mut self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'a, F>> {
        let t = self.batches.iter_mut().flat_map(|b| b.iter_for_commit()).collect::<Vec<_>>();
        t.into_iter().chain(self.mask_poly.clone().map(Into::into))
    }

    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when opening.
    pub fn iter_for_open(&'a self) -> impl Iterator<Item = &'a LabeledPolynomial<F>> {
        self.batches.iter().flat_map(|b| b.iter_for_open()).chain(self.mask_poly.as_ref())
    }

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        self.batches.iter().all(|b| b.matches_info(info))
            && self.mask_poly.as_ref().map_or(true, |p| Some(p.info()) == info.get(p.label()))
    }
}

#[derive(Debug, Clone)]
pub(in crate::snark::marlin) struct SingleEntry<'a, F: PrimeField> {
    /// The evaluations of `Az`.
    pub(super) z_a: LabeledPolynomialWithBasis<'a, F>,
    /// The evaluations of `Bz`.
    pub(super) z_b: LabeledPolynomialWithBasis<'a, F>,
    /// The LDE of `w`.
    pub(super) w_poly: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub(super) z_a_poly: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub(super) z_b_poly: LabeledPolynomial<F>,
}

impl<'a, F: PrimeField> SingleEntry<'a, F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    pub fn iter_for_commit(&mut self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'a, F>> {
        let w_poly = self.w_poly.clone();

        let z_a = self.z_a.clone();
        self.z_a = LabeledPolynomialWithBasis { polynomial: vec![], info: z_a.info().clone() };

        let z_b = self.z_b.clone();
        self.z_b = LabeledPolynomialWithBasis { polynomial: vec![], info: z_b.info().clone() };
        [w_poly.into(), z_a, z_b].into_iter()
    }

    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when opening.
    pub fn iter_for_open(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        [(&self.w_poly), &self.z_a_poly, &self.z_b_poly].into_iter()
    }

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        Some(self.w_poly.info()) == info.get(self.w_poly.label())
            && Some(self.z_a.info()) == info.get(self.z_a.label())
            && Some(self.z_b.info()) == info.get(self.z_b.label())
            && Some(self.z_a_poly.info()) == info.get(self.z_a_poly.label())
            && Some(self.z_b_poly.info()) == info.get(self.z_b_poly.label())
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

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        Some(self.h_1.info()) == info.get(self.h_1.label()) && Some(self.g_1.info()) == info.get(self.g_1.label())
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

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        Some(self.g_a.info()) == info.get(self.g_a.label())
            && Some(self.g_b.info()) == info.get(self.g_b.label())
            && Some(self.g_c.info()) == info.get(self.g_c.label())
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

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        Some(self.h_2.info()) == info.get(self.h_2.label())
    }
}
