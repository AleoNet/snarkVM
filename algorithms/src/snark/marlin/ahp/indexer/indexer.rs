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
    fft::EvaluationDomain,
    polycommit::sonic_pc::{PolynomialInfo, PolynomialLabel},
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
        map
    }
}
