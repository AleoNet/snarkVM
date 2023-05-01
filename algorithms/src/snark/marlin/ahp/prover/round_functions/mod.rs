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

use crate::snark::marlin::{
    ahp::{indexer::Circuit, AHPError, AHPForR1CS},
    prover,
    MarlinMode,
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::ConstraintSynthesizer;
use std::collections::BTreeMap;

use snarkvm_utilities::cfg_iter;
#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

mod first;
mod fourth;
mod second;
mod third;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Initialize the AHP prover.
    pub fn init_prover<'a, C: ConstraintSynthesizer<F>>(
        circuits_to_constraints: &BTreeMap<&'a Circuit<F, MM>, &[&C]>,
    ) -> Result<prover::State<'a, F, MM>, AHPError> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        let indices_and_assignments = cfg_iter!(circuits_to_constraints)
            .map(|(circuit, constraints)| {
                let num_non_zero_a = circuit.index_info.num_non_zero_a;
                let num_non_zero_b = circuit.index_info.num_non_zero_b;
                let num_non_zero_c = circuit.index_info.num_non_zero_c;

                let assignments = cfg_iter!(constraints)
                    .enumerate()
                    .map(|(_i, instance)| {
                        let constraint_time = start_timer!(|| format!(
                            "Generating constraints and witnesses for {:?} and index {_i}",
                            circuit.id
                        ));
                        let mut pcs = prover::ConstraintSystem::new();
                        instance.generate_constraints(&mut pcs)?;
                        end_timer!(constraint_time);

                        let padding_time = start_timer!(|| format!(
                            "Padding matrices to make them square for {:?} and index {_i}",
                            circuit.id
                        ));
                        crate::snark::marlin::ahp::matrices::pad_input_for_indexer_and_prover(&mut pcs);
                        pcs.make_matrices_square();
                        end_timer!(padding_time);

                        let prover::ConstraintSystem {
                            public_variables: padded_public_variables,
                            private_variables,
                            num_constraints,
                            num_public_variables,
                            num_private_variables,
                            ..
                        } = pcs;

                        assert_eq!(padded_public_variables.len(), num_public_variables);
                        assert!(padded_public_variables[0].is_one());
                        assert_eq!(private_variables.len(), num_private_variables);

                        if cfg!(debug_assertions) {
                            println!("Number of padded public variables in Prover::Init: {num_public_variables}");
                            println!("Number of private variables: {num_private_variables}");
                            println!("Number of constraints: {num_constraints}");
                            println!("Number of non-zero entries in A: {num_non_zero_a}");
                            println!("Number of non-zero entries in B: {num_non_zero_b}");
                            println!("Number of non-zero entries in C: {num_non_zero_c}");
                        }

                        if circuit.index_info.num_constraints != num_constraints
                            || circuit.index_info.num_variables != (num_public_variables + num_private_variables)
                        {
                            return Err(AHPError::InstanceDoesNotMatchIndex);
                        }

                        Self::formatted_public_input_is_admissible(&padded_public_variables)?;

                        let eval_z_a_time = start_timer!(|| format!("For {:?}, evaluating z_A_{_i}", circuit.id));
                        let z_a = cfg_iter!(circuit.a)
                            .map(|row| {
                                inner_product(&padded_public_variables, &private_variables, row, num_public_variables)
                            })
                            .collect();
                        end_timer!(eval_z_a_time);

                        let eval_z_b_time = start_timer!(|| format!("For {:?}, evaluating z_B_{_i}", circuit.id));
                        let z_b = cfg_iter!(circuit.b)
                            .map(|row| {
                                inner_product(&padded_public_variables, &private_variables, row, num_public_variables)
                            })
                            .collect();
                        end_timer!(eval_z_b_time);
                        end_timer!(init_time);
                        Ok(prover::Assignments::<F>(padded_public_variables, private_variables, z_a, z_b))
                    })
                    .collect::<Result<Vec<prover::Assignments<F>>, AHPError>>()?;
                Ok((*circuit, assignments))
            })
            .collect::<Result<BTreeMap<&'a Circuit<F, MM>, Vec<prover::Assignments<F>>>, AHPError>>()?;

        let state = prover::State::initialize(indices_and_assignments)?;

        Ok(state)
    }
}

fn inner_product<F: PrimeField>(
    public_variables: &[F],
    private_variables: &[F],
    row: &[(F, usize)],
    num_public_variables: usize,
) -> F {
    let mut result = F::zero();

    for &(ref coefficient, i) in row {
        // Fetch the variable.
        let variable = match i < num_public_variables {
            true => public_variables[i],
            false => private_variables[i - num_public_variables],
        };

        result += if coefficient.is_one() { variable } else { variable * coefficient };
    }

    result
}

#[test]
fn check_division_by_vanishing_poly_preserve_sparseness() {
    use crate::fft::{EvaluationDomain, Evaluations as EvaluationsOnDomain};
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_fields::{Field, One, Zero};

    let domain = EvaluationDomain::new(16).unwrap();
    let small_domain = EvaluationDomain::new(4).unwrap();
    let val = Fr::one().double().double().double() - Fr::one();
    let mut evals = (0..16).map(|pow| val.pow([pow])).collect::<Vec<_>>();
    for i in 0..4 {
        evals[4 * i] = Fr::zero();
    }
    let p = EvaluationsOnDomain::from_vec_and_domain(evals, domain).interpolate();
    assert_eq!(p.degree(), 15);
    let (p_div_v, p_mod_v) = p.divide_by_vanishing_poly(small_domain).unwrap();
    assert!(p_mod_v.is_zero());
    dbg!(p_div_v.degree());
    dbg!(p_div_v.evaluate_over_domain(domain));
}
