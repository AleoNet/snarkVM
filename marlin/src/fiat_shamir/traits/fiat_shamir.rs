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

use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    fields::FpGadget,
    utilities::{boolean::Boolean, uint::UInt8},
};
use snarkvm_nonnative::{params::OptimizationType, NonNativeFieldVar};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use rand_core::RngCore;

/// Trait for a Fiat-Shamir RNG.
pub trait FiatShamirRng<TargetField: PrimeField, BaseField: PrimeField>: RngCore {
    /// Initializes an RNG.
    fn new() -> Self;

    /// Takes in field elements.
    fn absorb_nonnative_field_elements(&mut self, elems: &[TargetField], ty: OptimizationType);
    /// Takes in field elements.
    fn absorb_native_field_elements<T: ToConstraintField<BaseField>>(&mut self, elems: &[T]);
    /// Takes in bytes.
    fn absorb_bytes(&mut self, elems: &[u8]);

    /// Takes out field elements.
    fn squeeze_nonnative_field_elements(&mut self, num: usize, ty: OptimizationType) -> Vec<TargetField>;
    /// Takes in field elements.
    fn squeeze_native_field_elements(&mut self, num: usize) -> Vec<BaseField>;
    /// Takes out field elements of 128 bits.
    fn squeeze_128_bits_nonnative_field_elements(&mut self, num: usize) -> Vec<TargetField>;
}

/// Vars for a RNG for use in a Fiat-Shamir transform.
pub trait FiatShamirRngVar<F: PrimeField, CF: PrimeField, PFS: FiatShamirRng<F, CF>>: Clone {
    /// Create a new RNG.
    fn new<CS: ConstraintSystem<CF>>(cs: CS) -> Self;

    /// Instantiate from a plaintext fs_rng.
    fn constant<CS: ConstraintSystem<CF>>(cs: CS, pfs: &PFS) -> Self;

    /// Take in field elements.
    fn absorb_nonnative_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[NonNativeFieldVar<F, CF>],
        ty: OptimizationType,
    ) -> Result<(), SynthesisError>;

    /// Take in field elements.
    fn absorb_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        elems: &[FpGadget<CF>],
    ) -> Result<(), SynthesisError>;

    /// Take in bytes.
    fn absorb_bytes<CS: ConstraintSystem<CF>>(&mut self, cs: CS, elems: &[UInt8]) -> Result<(), SynthesisError>;

    /// Output field elements.
    fn squeeze_native_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError>;

    /// Output field elements.
    fn squeeze_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements and the corresponding bits (this can reduce repeated computation).
    #[allow(clippy::type_complexity)]
    fn squeeze_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError>;

    /// Output field elements with only 128 bits.
    fn squeeze_128_bits_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError>;

    /// Output field elements with only 128 bits, and the corresponding bits (this can reduce
    /// repeated computation).
    #[allow(clippy::type_complexity)]
    fn squeeze_128_bits_field_elements_and_bits<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num: usize,
    ) -> Result<(Vec<NonNativeFieldVar<F, CF>>, Vec<Vec<Boolean>>), SynthesisError>;
}
