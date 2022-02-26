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

use crate::nonnative::{AllocatedNonNativeFieldMulResultVar, NonNativeFieldVar};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

/// An intermediate representation especially for the result of a multiplication, containing more limbs.
/// It is intended for advanced usage to improve the efficiency.
///
/// That is, instead of calling `mul`, one can call `mul_without_reduce` to
/// obtain this intermediate representation, which can still be added.
/// Then, one can call `reduce` to reduce it back to `NonNativeFieldVar`.
/// This may help cut the number of reduce operations.
#[derive(Debug)]
pub enum NonNativeFieldMulResultVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// as a constant
    Constant(TargetField),
    /// as an allocated gadget
    Variable(AllocatedNonNativeFieldMulResultVar<TargetField, BaseField>),
}

impl<TargetField: PrimeField, BaseField: PrimeField> NonNativeFieldMulResultVar<TargetField, BaseField> {
    /// Create a zero `NonNativeFieldMulResultVar` (used for additions)
    pub fn zero() -> Self {
        Self::Constant(TargetField::zero())
    }

    /// Create an `NonNativeFieldMulResultVar` from a constant
    pub fn constant(v: TargetField) -> Self {
        Self::Constant(v)
    }

    /// Reduce the `NonNativeFieldMulResultVar` back to NonNativeFieldVar
    pub fn reduce<CS: ConstraintSystem<BaseField>>(
        &self,
        cs: &mut CS,
    ) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(NonNativeFieldVar::Constant(*c)),
            Self::Variable(v) => Ok(NonNativeFieldVar::Var(v.reduce(cs)?)),
        }
    }

    /// Constructs a `NonNativeFieldMulResultVar` from a `NonNativeFieldVar`
    pub fn from_nonnative_field_gadget<CS: ConstraintSystem<BaseField>>(
        cs: &mut CS,
        src: &NonNativeFieldVar<TargetField, BaseField>,
    ) -> Result<Self, SynthesisError> {
        match src {
            NonNativeFieldVar::Constant(c) => Ok(NonNativeFieldMulResultVar::Constant(*c)),
            NonNativeFieldVar::Var(v) => Ok(NonNativeFieldMulResultVar::Variable(
                AllocatedNonNativeFieldMulResultVar::<TargetField, BaseField>::from_allocated_nonnative_field_gadget(
                    cs, v,
                )?,
            )),
        }
    }

    /// Add `NonNativeFieldMulResultVar` elements.
    pub fn add<CS: ConstraintSystem<BaseField>>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError> {
        match (self, other) {
            (Self::Constant(c1), Self::Constant(c2)) => Ok(Self::Constant(*c1 + c2)),
            (Self::Constant(c), Self::Variable(v)) | (Self::Variable(v), Self::Constant(c)) => {
                Ok(Self::Variable(v.add_constant(cs, c)?))
            }
            (Self::Variable(v1), Self::Variable(v2)) => Ok(Self::Variable(v1.add(cs, v2)?)),
        }
    }
}
