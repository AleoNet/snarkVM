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

use crate::snark::marlin::{
    ahp::{indexer::Circuit, AHPError, AHPForR1CS},
    prover,
    MarlinMode,
};
use itertools::Itertools;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::ConstraintSynthesizer;

use snarkvm_utilities::cfg_iter;
#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

mod first;
mod fourth;
mod second;
mod third;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Initialize the AHP prover.
    pub fn init_prover<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Circuit<F, MM>,
        circuits: &[C],
    ) -> Result<prover::State<'a, F, MM>, AHPError> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        // Perform matrix multiplications.
        let (padded_public_variables, private_variables, z_a, z_b) = cfg_iter!(circuits)
            .map(|circuit| {
                let constraint_time = start_timer!(|| "Generating constraints and witnesses");
                let mut pcs = prover::ConstraintSystem::new();
                circuit.generate_constraints(&mut pcs)?;
                end_timer!(constraint_time);

                let padding_time = start_timer!(|| "Padding matrices to make them square");
                crate::snark::marlin::ahp::matrices::pad_input_for_indexer_and_prover(&mut pcs);
                pcs.make_matrices_square();
                end_timer!(padding_time);

                let num_non_zero_a = index.index_info.num_non_zero_a;
                let num_non_zero_b = index.index_info.num_non_zero_b;
                let num_non_zero_c = index.index_info.num_non_zero_c;

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
                    println!("Number of padded public variables in Prover::Init: {}", num_public_variables);
                    println!("Number of private variables: {}", num_private_variables);
                    println!("Number of constraints: {}", num_constraints);
                    println!("Number of non-zero entries in A: {}", num_non_zero_a);
                    println!("Number of non-zero entries in B: {}", num_non_zero_b);
                    println!("Number of non-zero entries in C: {}", num_non_zero_c);
                }

                if index.index_info.num_constraints != num_constraints
                    || index.index_info.num_variables != (num_public_variables + num_private_variables)
                {
                    return Err(AHPError::InstanceDoesNotMatchIndex);
                }

                Self::formatted_public_input_is_admissible(&padded_public_variables)?;

                let eval_z_a_time = start_timer!(|| "Evaluating z_A");
                let z_a = cfg_iter!(index.a)
                    .map(|row| inner_product(&padded_public_variables, &private_variables, row, num_public_variables))
                    .collect();
                end_timer!(eval_z_a_time);

                let eval_z_b_time = start_timer!(|| "Evaluating z_B");
                let z_b = cfg_iter!(index.b)
                    .map(|row| inner_product(&padded_public_variables, &private_variables, row, num_public_variables))
                    .collect();
                end_timer!(eval_z_b_time);
                end_timer!(init_time);
                Ok((padded_public_variables, private_variables, z_a, z_b))
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .multiunzip();

        let mut state = prover::State::initialize(padded_public_variables, private_variables, index)?;
        state.z_a = Some(z_a);
        state.z_b = Some(z_b);

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
