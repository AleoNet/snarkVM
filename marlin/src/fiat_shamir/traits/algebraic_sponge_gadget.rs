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

use crate::{traits::AlgebraicSponge, Vec};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::fields::FpGadget;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

/// Trait for an algebraic sponge such as Poseidon.
pub trait AlgebraicSpongeVar<BaseField: PrimeField, PS: AlgebraicSponge<BaseField>>: Clone {
    /// Create the new sponge.
    fn new<CS: ConstraintSystem<BaseField>>(cs: CS) -> Self;

    /// Take in field elements.
    fn absorb<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        elems: &[FpGadget<BaseField>],
    ) -> Result<(), SynthesisError>;

    /// Output field elements.
    fn squeeze<CS: ConstraintSystem<BaseField>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<FpGadget<BaseField>>, SynthesisError>;
}
