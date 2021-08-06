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

use crate::ahp::AHPForR1CS;
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{errors::SerializationError, serialize::*, ToBytes};

use crate::Matrix;
use core::marker::PhantomData;
use derivative::Derivative;
use std::collections::BTreeSet;

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
    /// The total number of non-zero entries in the sum of all constraint matrices.
    pub num_non_zero: usize,

    #[doc(hidden)]
    pub f: PhantomData<F>,
}

pub(crate) fn sum_matrices<F: PrimeField>(a: &Matrix<F>, b: &Matrix<F>, c: &Matrix<F>) -> Vec<Vec<usize>> {
    a.iter()
        .zip(b)
        .zip(c)
        .map(|((row_a, row_b), row_c)| {
            row_a
                .iter()
                .map(|(_, i)| *i)
                .chain(row_b.iter().map(|(_, i)| *i))
                .chain(row_c.iter().map(|(_, i)| *i))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        })
        .collect()
}

impl<F: PrimeField> CircuitInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the AHP.
    pub fn max_degree(&self) -> usize {
        AHPForR1CS::<F>::max_degree(self.num_constraints, self.num_variables, self.num_non_zero).unwrap()
    }
}

impl<F: PrimeField> ToBytes for CircuitInfo<F> {
    fn write_le<W: Write>(&self, mut w: W) -> Result<(), std::io::Error> {
        (self.num_variables as u64).write_le(&mut w)?;
        (self.num_constraints as u64).write_le(&mut w)?;
        (self.num_non_zero as u64).write_le(&mut w)
    }
}
