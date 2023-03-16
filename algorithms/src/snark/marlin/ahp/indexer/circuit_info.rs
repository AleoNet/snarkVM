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

use crate::snark::marlin::{ahp::AHPForR1CS, MarlinMode};
use snarkvm_fields::PrimeField;
use snarkvm_utilities::{serialize::*, ToBytes};

use core::marker::PhantomData;

/// Information about the circuit, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd, CanonicalSerialize, CanonicalDeserialize)]
pub struct CircuitInfo<F: Sync + Send> {
    /// The number of public inputs after padding.
    pub num_public_inputs: usize,
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The number of non-zero entries in the A matrix.
    pub num_non_zero_a: usize,
    /// The number of non-zero entries in the B matrix.
    pub num_non_zero_b: usize,
    /// The number of non-zero entries in the C matrix.
    pub num_non_zero_c: usize,

    #[doc(hidden)]
    pub f: PhantomData<F>,
}

impl<F: PrimeField> CircuitInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the AHP.
    pub fn max_degree<MM: MarlinMode>(&self) -> usize {
        let max_non_zero = self.num_non_zero_a.max(self.num_non_zero_b).max(self.num_non_zero_c);
        AHPForR1CS::<F, MM>::max_degree(self.num_constraints, self.num_variables, max_non_zero).unwrap()
    }
}

impl<F: PrimeField> ToBytes for CircuitInfo<F> {
    fn write_le<W: Write>(&self, mut w: W) -> Result<(), io::Error> {
        (self.num_public_inputs as u64).write_le(&mut w)?;
        (self.num_variables as u64).write_le(&mut w)?;
        (self.num_constraints as u64).write_le(&mut w)?;
        (self.num_non_zero_a as u64).write_le(&mut w)?;
        (self.num_non_zero_b as u64).write_le(&mut w)?;
        (self.num_non_zero_c as u64).write_le(&mut w)
    }
}
