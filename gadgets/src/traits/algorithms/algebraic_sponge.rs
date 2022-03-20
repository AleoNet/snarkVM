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

use crate::FpGadget;
use snarkvm_algorithms::traits::AlgebraicSponge;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

/// The interface for a cryptographic sponge constraints on field `CF`.
/// A sponge can `absorb` or take in inputs and later `squeeze` or output bytes or field elements.
/// The outputs are dependent on previous `absorb` and `squeeze` calls.
pub trait AlgebraicSpongeVar<
    CF: PrimeField,
    S: AlgebraicSponge<CF, RATE, CAPACITY>,
    const RATE: usize,
    const CAPACITY: usize,
>: Clone
{
    /// Parameters used by the sponge.
    type Parameters;

    /// Initialize a new instance of the sponge.
    fn with_parameters<CS: ConstraintSystem<CF>>(cs: CS, params: &S::Parameters) -> Self;

    /// Absorb an input into the sponge.
    fn absorb<'a, CS: ConstraintSystem<CF>, I: Iterator<Item = &'a FpGadget<CF>>>(
        &mut self,
        cs: CS,
        input: I,
    ) -> Result<(), SynthesisError>;

    /// Squeeze `num_elements` field elements from the sponge.
    fn squeeze<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num_elements: usize,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError>;
}
