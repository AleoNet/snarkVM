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

use crate::fft::EvaluationDomain;
use snarkvm_fields::{batch_inversion, PrimeField};
use snarkvm_utilities::{cfg_into_iter, serialize::*};

use itertools::Itertools;
use std::collections::{BTreeMap, HashSet};

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

use super::verifier::QueryPoints;

/// Given two domains H and K such that H \subseteq K,
/// construct polynomial that outputs 0 on all elements in K \ H, but 1 on all elements of H.
pub(crate) trait SelectorPolynomial<F: PrimeField> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F;
}

impl<F: PrimeField> SelectorPolynomial<F> for EvaluationDomain<F> {
    fn evaluate_selector_polynomial(&self, other: EvaluationDomain<F>, point: F) -> F {
        let numerator = self.evaluate_vanishing_polynomial(point) * other.size_as_field_element;
        let denominator = other.evaluate_vanishing_polynomial(point) * self.size_as_field_element;
        numerator / denominator
    }
}

/// Precompute a batch of selectors at challenges. We batch:
/// - constraint domain selectors at alpha
/// - variable domain selectors at beta
/// - non_zero domain selectors at gamma
pub(crate) fn precompute_selectors<F: PrimeField>(
    max_constraint_domain: EvaluationDomain<F>,
    constraint_domains: HashSet<EvaluationDomain<F>>,
    max_variable_domain: EvaluationDomain<F>,
    variable_domains: HashSet<EvaluationDomain<F>>,
    max_non_zero_domain: EvaluationDomain<F>,
    non_zero_domains: HashSet<EvaluationDomain<F>>,
    challenges: QueryPoints<F>,
) -> BTreeMap<(u64, u64, F), F> {
    let max_domains = [max_constraint_domain, max_variable_domain, max_non_zero_domain];
    let domains = [constraint_domains, variable_domains, non_zero_domains];
    let (numerators, mut denominators, keys) = max_domains
        .into_iter()
        .zip_eq(domains)
        .zip_eq(challenges.into_iter())
        .flat_map(|((max_domain, domains), challenge)| {
            let max_domain_at_challenge = max_domain.evaluate_vanishing_polynomial(challenge);
            domains.into_iter().map(move |domain| {
                let domain_at_challenge = domain.evaluate_vanishing_polynomial(challenge);
                (
                    max_domain_at_challenge * domain.size_as_field_element,
                    domain_at_challenge * max_domain.size_as_field_element,
                    (max_domain.size, domain.size, challenge),
                )
            })
        })
        .multiunzip::<(Vec<F>, Vec<F>, Vec<(u64, u64, F)>)>();
    batch_inversion(&mut denominators);
    cfg_into_iter!(numerators).zip_eq(denominators).zip_eq(keys).map(|((num, denom), key)| (key, num * denom)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fft::Evaluations;
    use snarkvm_curves::bls12_377::fr::Fr;
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::rand::TestRng;

    #[test]
    fn test_alternator_polynomial() {
        let mut rng = TestRng::default();

        for i in 1..10 {
            for j in 1..i {
                let domain_i = EvaluationDomain::<Fr>::new(1 << i).unwrap();
                let domain_j = EvaluationDomain::<Fr>::new(1 << j).unwrap();
                let point = domain_j.sample_element_outside_domain(&mut rng);
                let j_elements = domain_j.elements().collect::<Vec<_>>();
                let slow_selector = {
                    let evals = domain_i
                        .elements()
                        .map(|e| if j_elements.contains(&e) { Fr::one() } else { Fr::zero() })
                        .collect();
                    Evaluations::from_vec_and_domain(evals, domain_i).interpolate()
                };
                assert_eq!(slow_selector.evaluate(point), domain_i.evaluate_selector_polynomial(domain_j, point));

                for element in domain_i.elements() {
                    if j_elements.contains(&element) {
                        assert_eq!(slow_selector.evaluate(element), Fr::one(), "failed for {i} vs {j}");
                    } else {
                        assert_eq!(slow_selector.evaluate(element), Fr::zero());
                    }
                }
            }
        }
    }
}
