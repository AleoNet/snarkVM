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

use crate::{
    ahp::{
        indexer::{Circuit, CircuitInfo, IndexerConstraintSystem},
        matrices::arithmetize_matrix,
        AHPError,
        AHPForR1CS,
    },
    marlin::MarlinMode,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::errors::SynthesisError;

use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem};

use crate::{num_non_zero, sum_matrices};
use core::marker::PhantomData;

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
        crate::ahp::matrices::pad_input_for_indexer_and_prover(&mut ics);
        ics.make_matrices_square();

        let a = ics.a_matrix();
        let b = ics.b_matrix();
        let c = ics.c_matrix();

        let joint_matrix = sum_matrices(&a, &b, &c);

        // balance_matrices(&mut a, &mut b);
        end_timer!(padding_time);

        let num_padded_public_variables = ics.num_public_variables();
        let num_private_variables = ics.num_private_variables();
        let num_constraints = ics.num_constraints();
        let num_non_zero = num_non_zero(&joint_matrix);
        let num_variables = num_padded_public_variables + num_private_variables;

        if cfg!(debug_assertions) {
            println!("Number of padded public variables: {}", num_padded_public_variables);
            println!("Number of private variables: {}", num_private_variables);
            println!("Number of num_constraints: {}", num_constraints);
            println!("Number of num_non_zero: {}", num_non_zero);
        }

        if num_constraints != num_variables {
            eprintln!("Number of padded public variables: {}", num_padded_public_variables);
            eprintln!("Number of private variables: {}", num_private_variables);
            eprintln!("Number of num_constraints: {}", num_constraints);
            eprintln!("Number of num_non_zero: {}", num_non_zero);
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
            EvaluationDomain::new(num_padded_public_variables).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let joint_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let joint_arith = arithmetize_matrix(&joint_matrix, &a, &b, &c, domain_k, domain_h, x_domain);
        end_timer!(joint_arithmetization_time);

        end_timer!(index_time);
        Ok(Circuit {
            index_info,

            a,
            b,
            c,

            joint_arith,
            mode: PhantomData,
        })
    }
}
