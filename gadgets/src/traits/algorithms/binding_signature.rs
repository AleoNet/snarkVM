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
    boolean::Boolean,
    traits::{alloc::AllocGadget, eq::EqGadget, CommitmentGadget},
    uint::UInt8,
    ToBytesGadget,
};

use snarkvm_algorithms::traits::CommitmentScheme;
use snarkvm_curves::{Group, ProjectiveCurve};
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use std::fmt::Debug;

pub trait BindingSignatureGadget<C: CommitmentScheme, F: Field, G: Group + ProjectiveCurve> {
    type CommitmentGadget: CommitmentGadget<C, F> + Clone;
    type OutputGadget: EqGadget<F> + ToBytesGadget<F> + AllocGadget<G, F> + Clone + Sized + Debug;
    type RandomnessGadget: AllocGadget<C::Randomness, F> + Clone;

    fn check_value_balance_commitment_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        commitment_scheme: &Self::CommitmentGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;

    fn check_binding_signature_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        partial_bvk: &Self::OutputGadget,
        value_balance_comm: &Self::OutputGadget,
        is_negative: &Boolean,
        c: &Self::RandomnessGadget,
        affine_r: &Self::OutputGadget,
        recommit: &Self::OutputGadget,
    ) -> Result<(), SynthesisError>;
}
