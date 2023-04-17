// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use crate::{
    polycommit::sonic_pc::{LabeledPolynomial, LabeledPolynomialWithBasis, PolynomialInfo, PolynomialLabel},
    snark::marlin::CircuitId,
};

/// The first set of prover oracles.
#[derive(Debug, Clone)]
pub struct FirstOracles<F: PrimeField> {
    pub(in crate::snark::marlin) batches: BTreeMap<CircuitId, Vec<SingleEntry<F>>>,
    /// The sum-check hiding polynomial.
    pub mask_poly: Option<LabeledPolynomial<F>>,
}

impl<F: PrimeField> FirstOracles<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    #[allow(clippy::needless_collect)]
    pub fn iter_for_commit(&mut self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'static, F>> {
        let t =
            self.batches.values_mut().flat_map(|b| b.iter_mut()).flat_map(|b| b.iter_for_commit()).collect::<Vec<_>>();
        t.into_iter().chain(self.mask_poly.clone().map(Into::into))
    }

    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when opening.
    pub fn iter_for_open(&self) -> impl Iterator<Item = &'_ LabeledPolynomial<F>> {
        self.batches.values().flat_map(|b| b.iter()).flat_map(|b| b.iter_for_open()).chain(self.mask_poly.as_ref())
    }

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        self.batches.values().all(|b| b.iter().all(|b| b.matches_info(info)))
            && self.mask_poly.as_ref().map_or(true, |p| Some(p.info()) == info.get(p.label()))
    }
}

#[derive(Debug, Clone)]
pub(in crate::snark::marlin) struct SingleEntry<F: PrimeField> {
    /// The evaluations of `Az`.
    pub(super) z_a: LabeledPolynomialWithBasis<'static, F>,
    /// The evaluations of `Bz`.
    pub(super) z_b: LabeledPolynomialWithBasis<'static, F>,
    /// The LDE of `w`.
    pub(super) w_poly: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub(super) z_a_poly: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub(super) z_b_poly: LabeledPolynomial<F>,
}

impl<F: PrimeField> SingleEntry<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    /// Intended for use when committing.
    pub fn iter_for_commit(&mut self) -> impl Iterator<Item = LabeledPolynomialWithBasis<'static, F>> {
        let w_poly = self.w_poly.clone();

        let mut z_a_copy = LabeledPolynomialWithBasis { polynomial: vec![], info: self.z_a.info().clone() };
        std::mem::swap(&mut self.z_a, &mut z_a_copy);

        let mut z_b_copy = LabeledPolynomialWithBasis { polynomial: vec![], info: self.z_b.info().clone() };
        std::mem::swap(&mut self.z_b, &mut z_b_copy);
        [w_poly.into(), z_a_copy, z_b_copy].into_iter()
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
    pub(super) gs: BTreeMap<CircuitId, MatrixGs<F>>,
}

#[derive(Debug)]
pub(super) struct MatrixGs<F: PrimeField> {
    /// The polynomial `g_a` resulting from the second sumcheck.
    pub(super) g_a: LabeledPolynomial<F>,
    /// The polynomial `g_b` resulting from the second sumcheck.
    pub(super) g_b: LabeledPolynomial<F>,
    /// The polynomial `g_c` resulting from the second sumcheck.
    pub(super) g_c: LabeledPolynomial<F>,
}

impl<F: PrimeField> MatrixGs<F> {
    pub fn matches_matrix_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        Some(self.g_a.info()) == info.get(self.g_a.label())
            && Some(self.g_b.info()) == info.get(self.g_b.label())
            && Some(self.g_c.info()) == info.get(self.g_c.label())
    }
}

impl<F: PrimeField> ThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        self.gs.values().flat_map(|gs| [&gs.g_a, &gs.g_b, &gs.g_c].into_iter())
    }

    pub fn matches_info(&self, info: &BTreeMap<PolynomialLabel, PolynomialInfo>) -> bool {
        self.gs.values().all(|b| b.matches_matrix_info(info))
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
