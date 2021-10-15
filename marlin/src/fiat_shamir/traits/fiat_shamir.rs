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

use crate::{fiat_shamir::FiatShamirError, Vec};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::nonnative::params::OptimizationType;

use core::fmt::Debug;
use rand_core::RngCore;

// TODO (raychu86): Remove unnecessary Result types

/// Trait for a Fiat-Shamir RNG.
pub trait FiatShamirRng<TargetField: PrimeField, BaseField: PrimeField>: Clone + Debug + RngCore {
    /// Initializes an RNG.
    fn new() -> Self;

    /// Takes in field elements.
    fn absorb_nonnative_field_elements(&mut self, elements: &[TargetField], ty: OptimizationType);

    /// Takes in field elements.
    fn absorb_native_field_elements<T: ToConstraintField<BaseField>>(&mut self, elements: &[T]);

    /// Takes in bytes.
    fn absorb_bytes(&mut self, elements: &[u8]);

    /// Takes out field elements.
    fn squeeze_nonnative_field_elements(
        &mut self,
        num: usize,
        ty: OptimizationType,
    ) -> Result<Vec<TargetField>, FiatShamirError>;

    /// Takes in field elements.
    fn squeeze_native_field_elements(&mut self, num: usize) -> Result<Vec<BaseField>, FiatShamirError>;

    /// Takes out field elements of 128 bits.
    fn squeeze_128_bits_nonnative_field_elements(&mut self, num: usize) -> Result<Vec<TargetField>, FiatShamirError>;
}
