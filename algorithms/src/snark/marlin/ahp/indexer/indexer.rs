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

use crate::{
    fft::{EvaluationDomain, Evaluations},
    polycommit::sonic_pc::{LabeledPolynomial, PolynomialInfo, PolynomialLabel},
    snark::marlin::{
        ahp::{
            indexer::{Circuit, CircuitInfo, ConstraintSystem as IndexerConstraintSystem},
            matrices::arithmetize_matrix,
            AHPError,
            AHPForR1CS,
        },
        num_non_zero,
        MarlinMode,
    },
};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSynthesizer, ConstraintSystem};

use core::marker::PhantomData;
use std::collections::BTreeMap;

#[cfg(not(feature = "std"))]
use snarkvm_utilities::println;

impl<F: PrimeField, MM: MarlinMode> AHPForR1CS<F, MM> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: &C) -> Result<Circuit<F, MM>, AHPError> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        crate::snark::marlin::ahp::matrices::pad_input_for_indexer_and_prover(&mut ics);
        ics.make_matrices_square();

        let a = ics.a_matrix();
        let b = ics.b_matrix();
        let c = ics.c_matrix();

        // balance_matrices(&mut a, &mut b);
        end_timer!(padding_time);

        let num_padded_public_variables = ics.num_public_variables();
        let num_private_variables = ics.num_private_variables();
        let num_constraints = ics.num_constraints();
        let num_non_zero_a = num_non_zero(&a);
        let num_non_zero_b = num_non_zero(&b);
        let num_non_zero_c = num_non_zero(&c);
        let num_variables = num_padded_public_variables + num_private_variables;

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {}", num_padded_public_variables);
            println!("Number of private variables: {}", num_private_variables);
            println!("Number of num_constraints: {}", num_constraints);
            println!("Number of non-zero entries in A: {}", num_non_zero_a);
            println!("Number of non-zero entries in B: {}", num_non_zero_b);
            println!("Number of non-zero entries in C: {}", num_non_zero_c);
        }

        if num_constraints != num_variables {
            eprintln!("Number of padded public variables: {}", num_padded_public_variables);
            eprintln!("Number of private variables: {}", num_private_variables);
            eprintln!("Number of num_constraints: {}", num_constraints);
            eprintln!("Number of non-zero entries in A: {}", num_non_zero_a);
            eprintln!("Number of non-zero entries in B: {}", num_non_zero_b);
            eprintln!("Number of non-zero entries in C: {}", num_non_zero_c);
            return Err(AHPError::NonSquareMatrix);
        }

        Self::num_formatted_public_inputs_is_admissible(num_padded_public_variables)?;

        let index_info = CircuitInfo {
            num_public_inputs: num_padded_public_variables,
            num_variables,
            num_constraints,
            num_non_zero_a,
            num_non_zero_b,
            num_non_zero_c,
            f: PhantomData,
        };

        let constraint_domain =
            EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let input_domain =
            EvaluationDomain::new(num_padded_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let non_zero_a_domain =
            EvaluationDomain::new(num_non_zero_a).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_b_domain =
            EvaluationDomain::new(num_non_zero_b).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_c_domain =
            EvaluationDomain::new(num_non_zero_c).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let joint_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_arith = arithmetize_matrix(&a, "a", non_zero_a_domain, constraint_domain, input_domain);
        let b_arith = arithmetize_matrix(&b, "b", non_zero_b_domain, constraint_domain, input_domain);
        let c_arith = arithmetize_matrix(&c, "c", non_zero_c_domain, constraint_domain, input_domain);
        end_timer!(joint_arithmetization_time);

        let fft_precomp_time = start_timer!(|| "Precomputing roots of unity");

        let (fft_precomputation, ifft_precomputation) = Self::fft_precomputation(
            constraint_domain.size(),
            non_zero_a_domain.size(),
            non_zero_b_domain.size(),
            non_zero_c_domain.size(),
        )
        .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        end_timer!(fft_precomp_time);

        let mut mul_constraint_evals = vec![F::zero(); num_constraints];
        ics.mul_constraints.iter().for_each(|index| mul_constraint_evals[*index] = F::one());
        let s_m_evals = Evaluations::from_vec_and_domain(mul_constraint_evals, constraint_domain);
        let s_m = LabeledPolynomial::new(
            "s_m".to_string(),
            s_m_evals.interpolate_with_pc_by_ref(&ifft_precomputation),
            None,
            None,
        );

        let mut lookup_constraint_evals = vec![F::zero(); num_constraints];
        let mut lookup_tables = vec![];
        ics.lookup_constraints.iter().for_each(|entry| {
            lookup_tables.push(entry.table.clone());
            entry.indices.iter().for_each(|index| lookup_constraint_evals[*index] = F::one());
        });
        let s_l_evals = Evaluations::from_vec_and_domain(lookup_constraint_evals.clone(), constraint_domain);
        let s_l = LabeledPolynomial::new(
            "s_l".to_string(),
            s_l_evals.interpolate_with_pc_by_ref(&ifft_precomputation),
            None,
            None,
        );

        let mut l_1_evals = vec![F::zero(); constraint_domain.size()];
        l_1_evals[0] = F::one();
        let l_1 = LabeledPolynomial::new(
            "l_1".to_string(),
            Evaluations::from_vec_and_domain(l_1_evals, constraint_domain)
                .interpolate_with_pc_by_ref(&ifft_precomputation),
            None,
            None,
        );

        end_timer!(index_time);
        Ok(Circuit {
            index_info,
            a,
            b,
            c,
            a_arith,
            b_arith,
            c_arith,
            fft_precomputation,
            ifft_precomputation,
            s_m,
            s_l,
            s_l_evals: lookup_constraint_evals,
            l_1,
            lookup_tables,
            mode: PhantomData,
        })
    }

    pub fn index_polynomial_info() -> BTreeMap<PolynomialLabel, PolynomialInfo> {
        let mut map = BTreeMap::new();
        for matrix in ["a", "b", "c"] {
            map.insert(format!("row_{matrix}"), PolynomialInfo::new(format!("row_{matrix}"), None, None));
            map.insert(format!("col_{matrix}"), PolynomialInfo::new(format!("col_{matrix}"), None, None));
            map.insert(format!("val_{matrix}"), PolynomialInfo::new(format!("val_{matrix}"), None, None));
            map.insert(format!("row_col_{matrix}"), PolynomialInfo::new(format!("row_col_{matrix}"), None, None));
        }
        map.insert("s_m".to_string(), PolynomialInfo::new("s_m".to_string(), None, None));
        map.insert("s_l".to_string(), PolynomialInfo::new("s_l".to_string(), None, None));
        map.insert("l_1".to_string(), PolynomialInfo::new("l_1".to_string(), None, None));
        map
    }
}
