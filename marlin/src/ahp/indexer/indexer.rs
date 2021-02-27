// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::ahp::indexer::{Circuit, CircuitInfo, IndexerConstraintSystem};
use crate::ahp::matrices::arithmetize_matrix;
use crate::ahp::{AHPError, AHPForR1CS};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_curves::traits::PrimeField;
use snarkvm_r1cs::errors::SynthesisError;

use snarkvm_gadgets::traits::r1cs::{ConstraintSynthesizer, ConstraintSystem};

use core::marker::PhantomData;

impl<F: PrimeField> AHPForR1CS<F> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: &C) -> Result<Circuit<F>, AHPError> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        crate::ahp::matrices::pad_input_for_indexer_and_prover(&mut ics);
        ics.make_matrices_square();
        // balance_matrices(&mut a, &mut b);
        let mut a = ics.a_matrix();
        let mut b = ics.b_matrix();
        let mut c = ics.c_matrix();
        crate::ahp::matrices::balance_matrices(&mut a, &mut b);
        end_timer!(padding_time);

        let num_padded_public_variables = ics.num_public_variables();
        let num_private_variables = ics.num_private_variables();
        let num_constraints = ics.num_constraints();
        let num_non_zero = ics.num_non_zero();
        let num_variables = num_padded_public_variables + num_private_variables;

        if num_constraints != num_variables {
            eprintln!("number of padded public variables: {}", num_padded_public_variables);
            eprintln!("number of private variables: {}", num_private_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", num_non_zero);
            return Err(AHPError::NonSquareMatrix);
        }

        if !Self::num_formatted_public_inputs_is_admissible(num_padded_public_variables) {
            return Err(AHPError::InvalidPublicInputLength);
        }

        let index_info = CircuitInfo {
            num_variables,
            num_constraints,
            num_non_zero,
            f: PhantomData,
        };

        let domain_h = EvaluationDomain::new(num_constraints).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = EvaluationDomain::new(num_non_zero).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let x_domain =
            EvaluationDomain::<F>::new(num_padded_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let b_domain =
            EvaluationDomain::<F>::new(3 * domain_k.size() - 3).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_star_arith = arithmetize_matrix("a", &mut a, domain_k, domain_h, x_domain, b_domain);
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_star_arith = arithmetize_matrix("b", &mut b, domain_k, domain_h, x_domain, b_domain);
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_star_arith = arithmetize_matrix("c", &mut c, domain_k, domain_h, x_domain, b_domain);
        end_timer!(c_arithmetization_time);

        end_timer!(index_time);
        Ok(Circuit {
            index_info,

            a,
            b,
            c,

            a_star_arith,
            b_star_arith,
            c_star_arith,
        })
    }
}
