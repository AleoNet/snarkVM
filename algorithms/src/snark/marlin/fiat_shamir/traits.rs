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

use crate::snark::marlin::{fiat_shamir::FiatShamirError, params::OptimizationType};
use snarkvm_fields::{PrimeField, ToConstraintField};

use core::fmt::Debug;
use smallvec::SmallVec;

// TODO (raychu86): Remove unnecessary Result types

/// Trait for a Fiat-Shamir RNG.
pub trait FiatShamirRng<TargetField: PrimeField, BaseField: PrimeField>: Clone + Debug {
    type Parameters;

    /// Initializes an RNG.
    fn new() -> Self;

    /// Takes in field elements.
    fn absorb_nonnative_field_elements(
        &mut self,
        elements: impl IntoIterator<Item = TargetField>,
        ty: OptimizationType,
    );

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
    fn squeeze_native_field_elements(&mut self, num: usize) -> Result<SmallVec<[BaseField; 10]>, FiatShamirError>;

    /// Takes out field elements of 168 bits.
    fn squeeze_short_nonnative_field_elements(&mut self, num: usize) -> Result<Vec<TargetField>, FiatShamirError>;

    /// Takes out a field element of 168 bits.
    fn squeeze_short_nonnative_field_element(&mut self) -> Result<TargetField, FiatShamirError> {
        self.squeeze_short_nonnative_field_elements(1).map(|v| v[0])
    }
}
