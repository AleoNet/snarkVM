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

#![allow(non_snake_case)]

mod constraint_system;
pub(crate) use constraint_system::*;

use crate::{
    ahp::{
        indexer::IndexerConstraintSystem,
        matrices::{arithmetize_matrix, MatrixArithmetization},
        AHPError,
        AHPForR1CS,
    },
    Vec,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_errors::{gadgets::SynthesisError, serialization::SerializationError};
use snarkvm_models::{
    curves::PrimeField,
    gadgets::r1cs::{ConstraintSynthesizer, ConstraintSystem},
};
use snarkvm_polycommit::LabeledPolynomial;
use snarkvm_utilities::{serialize::*, ToBytes};

use core::marker::PhantomData;
use derivative::Derivative;

/// Information about the circuit, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitInfo<F> {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in any constraint matrix.
    pub num_non_zero: usize,

    #[doc(hidden)]
    pub f: PhantomData<F>,
}

impl<F: PrimeField> CircuitInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the AHP.
    pub fn max_degree(&self) -> usize {
        AHPForR1CS::<F>::max_degree(self.num_constraints, self.num_variables, self.num_non_zero).unwrap()
    }
}

impl<F: PrimeField> ToBytes for CircuitInfo<F> {
    fn write<W: Write>(&self, mut w: W) -> Result<(), std::io::Error> {
        (self.num_variables as u64).write(&mut w)?;
        (self.num_constraints as u64).write(&mut w)?;
        (self.num_non_zero as u64).write(&mut w)
    }
}

/// Represents a matrix.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
/// The indexed version of the constraint system.
/// This struct contains three kinds of objects:
/// 1) `index_info` is information about the index, such as the size of the
///     public input
/// 2) `{a,b,c}` are the matrices defining the R1CS instance
/// 3) `{a,b,c}_star_arith` are structs containing information about A^*, B^*, and C^*,
/// which are matrices defined as `M^*(i, j) = M(j, i) * u_H(j, j)`.
pub struct Circuit<F: PrimeField> {
    /// Information about the indexed circuit.
    pub index_info: CircuitInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,

    /// Arithmetization of the A* matrix.
    pub a_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the B* matrix.
    pub b_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the C* matrix.
    pub c_star_arith: MatrixArithmetization<F>,
}

impl<F: PrimeField> Circuit<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self) -> usize {
        self.index_info.max_degree()
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![
            &self.a_star_arith.row,
            &self.a_star_arith.col,
            &self.a_star_arith.val,
            &self.a_star_arith.row_col,
            &self.b_star_arith.row,
            &self.b_star_arith.col,
            &self.b_star_arith.val,
            &self.b_star_arith.row_col,
            &self.c_star_arith.row,
            &self.c_star_arith.col,
            &self.c_star_arith.val,
            &self.c_star_arith.row_col,
        ]
        .into_iter()
    }
}

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
