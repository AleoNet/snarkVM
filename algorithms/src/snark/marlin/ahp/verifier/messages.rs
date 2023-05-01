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

use snarkvm_fields::PrimeField;

use crate::snark::marlin::{witness_label, CircuitId, MarlinMode};
use itertools::Itertools;
use std::collections::BTreeMap;

/// Randomizers used to combine circuit-specific and instance-specific elements in the AHP sumchecks
#[derive(Clone, Debug)]
pub(crate) struct BatchCombiners<F> {
    pub(crate) circuit_combiner: F,
    pub(crate) instance_combiners: Vec<F>,
}

/// First message of the verifier.
/// We only need randomizers for B and C to get a linear combination for {A,B,C}
#[derive(Clone, Debug)]
pub struct FirstMessage<F: PrimeField> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `B`.
    pub eta_b: F,
    /// Randomizer for the lincheck for `C`.
    pub eta_c: F,
    /// Randomizers for combining vectors from the batch
    pub(crate) batch_combiners: BTreeMap<CircuitId, BatchCombiners<F>>,
}

/// Second verifier message.
#[derive(Copy, Clone, Debug)]
pub struct SecondMessage<F> {
    /// Query for the second round of polynomials.
    pub beta: F,
}

/// Third message of the verifier.
#[derive(Clone, Debug)]
pub struct ThirdMessage<F> {
    /// Randomizers for the h-polynomial for `A_i`, `B_i`, `C_i` for circuit i.
    pub delta_a: Vec<F>,
    pub delta_b: Vec<F>,
    pub delta_c: Vec<F>,
}

impl<F: PrimeField> ThirdMessage<F> {
    pub fn into_iter(self) -> impl Iterator<Item = F> {
        self.delta_a
            .into_iter()
            .zip_eq(self.delta_b.into_iter())
            .zip_eq(self.delta_c.into_iter())
            .flat_map(|((r_a, r_b), r_c)| [r_a, r_b, r_c])
    }
}

/// Query set of the verifier.
#[derive(Clone, Debug)]
pub struct QuerySet<F: PrimeField> {
    pub batch_sizes: BTreeMap<CircuitId, usize>,
    pub g_1_query: (String, F),
    pub z_b_query: (String, F),
    pub lincheck_sumcheck_query: (String, F),

    pub g_a_query: (String, F),
    pub g_b_query: (String, F),
    pub g_c_query: (String, F),
    pub matrix_sumcheck_query: (String, F),
}

impl<F: PrimeField> QuerySet<F> {
    pub fn new<MM: MarlinMode>(state: &super::State<F, MM>) -> Self {
        let beta = state.second_round_message.unwrap().beta;
        let gamma = state.gamma.unwrap();
        // For the first linear combination
        // Lincheck sumcheck test:
        //   s(beta) + r(alpha, beta) * (sum_i batch_combiner_i (sum_M eta_M z_M(beta))) - t(beta) * z(beta)
        // = h_1(beta) * v_H(beta) + beta * g_1(beta)
        //
        // Note that z is the interpolation of x || w, so it equals x + v_X * w
        // We also use an optimization: instead of explicitly calculating z_c, we
        // use the "virtual oracle" z_a * z_b
        Self {
            batch_sizes: state.circuit_specific_states.iter().map(|(c, s)| (*c, s.batch_size)).collect(),
            g_1_query: ("beta".into(), beta),
            z_b_query: ("beta".into(), beta),
            lincheck_sumcheck_query: ("beta".into(), beta),

            g_a_query: ("gamma".into(), gamma),
            g_b_query: ("gamma".into(), gamma),
            g_c_query: ("gamma".into(), gamma),
            matrix_sumcheck_query: ("gamma".into(), gamma),
        }
    }

    /// Returns a `BTreeSet` containing elements of the form
    /// `(polynomial_label, (query_label, query))`.
    pub fn to_set(&self) -> crate::polycommit::sonic_pc::QuerySet<F> {
        let mut query_set = crate::polycommit::sonic_pc::QuerySet::new();
        for (&circuit_id, &batch_size) in self.batch_sizes.iter() {
            for j in 0..batch_size {
                query_set.insert((witness_label(circuit_id, "z_b", j), self.z_b_query.clone()));
            }
            query_set.insert((witness_label(circuit_id, "g_a", 0), self.g_a_query.clone()));
            query_set.insert((witness_label(circuit_id, "g_b", 0), self.g_b_query.clone()));
            query_set.insert((witness_label(circuit_id, "g_c", 0), self.g_c_query.clone()));
        }
        query_set.insert(("g_1".into(), self.g_1_query.clone()));
        query_set.insert(("lincheck_sumcheck".into(), self.lincheck_sumcheck_query.clone()));
        query_set.insert(("matrix_sumcheck".into(), self.matrix_sumcheck_query.clone()));
        query_set
    }
}
