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

use snarkvm_fields::PrimeField;

use crate::snark::varuna::{witness_label, BatchSize, CircuitId, SNARKMode};
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
    /// Randomizers for combining checks from the batch
    pub(crate) batch_combiners: BTreeMap<CircuitId, BatchCombiners<F>>,
    /// Randomizer to combine lookup components
    pub(crate) zeta: F,
    /// Challenge for lookup
    pub(crate) theta: F,
}

/// Lookup verifier message.
#[derive(Copy, Clone, Debug)]
pub struct LookupMessage<F> {
    /// Query for the lookup round of polynomials.
    pub phi: F,
}

/// Second verifier message.
#[derive(Copy, Clone, Debug)]
pub struct SecondMessage<F> {
    /// Query for lineval.
    pub alpha: F,
    /// Randomizer for the lineval for `B`.
    pub eta_b: F,
    /// Randomizer for the lineval for `C`.
    pub eta_c: F,
}

/// Third verifier message.
#[derive(Copy, Clone, Debug)]
pub struct ThirdMessage<F> {
    /// Query for the third round of polynomials.
    pub beta: F,
}

/// Fourth message of the verifier.
#[derive(Clone, Debug)]
pub struct FourthMessage<F> {
    /// Randomizers for the h-polynomial for `A_i`, `B_i`, `C_i` for circuit i.
    pub delta_a: Vec<F>,
    pub delta_b: Vec<F>,
    pub delta_c: Vec<F>,
}

impl<F: PrimeField> FourthMessage<F> {
    pub fn into_iter(self) -> impl Iterator<Item = F> {
        self.delta_a
            .into_iter()
            .zip_eq(self.delta_b.into_iter())
            .zip_eq(self.delta_c.into_iter())
            .flat_map(|((r_a, r_b), r_c)| [r_a, r_b, r_c])
    }
}

/// Fifth message of the verifier.
#[derive(Clone, Debug)]
pub struct FifthMessage<F> {
    pub gamma: F,
}

/// Query set of the verifier.
#[derive(Clone, Debug)]
pub struct QuerySet<F: PrimeField> {
    pub batch_sizes: BTreeMap<CircuitId, BatchSize>,

    pub s_mul_query: (String, F),
    pub s_lookup_query: (String, F),
    pub g_0_query: (String, F),
    pub rowcheck_sumcheck_query: (String, F),

    pub g_1_query: (String, F),
    pub lineval_sumcheck_query: (String, F),

    pub g_a_query: (String, F),
    pub g_b_query: (String, F),
    pub g_c_query: (String, F),
    pub matrix_sumcheck_query: (String, F),
}

impl<F: PrimeField> QuerySet<F> {
    pub fn new<MM: SNARKMode>(state: &super::State<F, MM>) -> Self {
        let alpha = state.second_round_message.as_ref().unwrap().alpha;
        let beta = state.third_round_message.unwrap().beta;
        let gamma = state.fifth_round_message.as_ref().unwrap().gamma;
        // The rowcheck_sumcheck, lineval_sumcheck and matrix_sumcheck are linear combinations ("virtual oracles") of other oracles
        // The rowcheck_sumcheck evaluates whether our polynomial constraints (e.g. R1CS) hold
        // The lineval_sumcheck evaluates whether those constraints hold on an evaluation of assignments multiplied by constraint matrices
        // The matrix_sumcheck evaluates whether the lineval sumcheck holds on an evaluation of constraint matrices over the domain of non-zero entries
        Self {
            batch_sizes: state.circuit_specific_states.iter().map(|(c, s)| (*c, s.batch_size.clone())).collect(),

            s_mul_query: ("alpha".into(), alpha),
            s_lookup_query: ("alpha".into(), alpha),
            g_0_query: ("alpha".into(), alpha),
            rowcheck_sumcheck_query: ("alpha".into(), alpha),

            g_1_query: ("beta".into(), beta),
            lineval_sumcheck_query: ("beta".into(), beta),

            g_a_query: ("gamma".into(), gamma),
            g_b_query: ("gamma".into(), gamma),
            g_c_query: ("gamma".into(), gamma),
            matrix_sumcheck_query: ("gamma".into(), gamma),
        }
    }

    // TODO: make a Query object and update descriptions
    /// Returns a `BTreeSet` containing elements of the form
    /// `(polynomial_label, (query_label, query))`.
    pub fn to_set(&self) -> crate::polycommit::sonic_pc::QuerySet<F> {
        let mut query_set = crate::polycommit::sonic_pc::QuerySet::new();
        let mut lookup_circuit_index = 0;
        let mut lookup_instance_index = 0;
        for (circuit_index, (&circuit_id, batch_size)) in self.batch_sizes.iter().enumerate() {
            query_set.insert((witness_label(circuit_id, "g_a", 0), (circuit_index, self.g_a_query.clone())));
            query_set.insert((witness_label(circuit_id, "g_b", 0), (circuit_index, self.g_b_query.clone())));
            query_set.insert((witness_label(circuit_id, "g_c", 0), (circuit_index, self.g_c_query.clone())));
            if batch_size.lookups_used {
                query_set.insert((
                    witness_label(circuit_id, "s_lookup", 0),
                    (lookup_circuit_index, self.s_lookup_query.clone()),
                ));
                query_set
                    .insert((witness_label(circuit_id, "s_mul", 0), (lookup_circuit_index, self.s_mul_query.clone())));
                for j in 0..batch_size.num_instances {
                    query_set
                        .insert((witness_label(circuit_id, "g_0", j), (lookup_instance_index, self.g_0_query.clone())));
                    lookup_instance_index += 1;
                }
                lookup_circuit_index += 1;
            }
        }
        query_set.insert(("g_1".into(), (0, self.g_1_query.clone())));
        query_set.insert(("rowcheck_sumcheck".into(), (0, self.rowcheck_sumcheck_query.clone())));
        query_set.insert(("lineval_sumcheck".into(), (0, self.lineval_sumcheck_query.clone())));
        query_set.insert(("matrix_sumcheck".into(), (0, self.matrix_sumcheck_query.clone())));
        query_set
    }
}
