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

use std::fmt::Debug;

use snarkvm_algorithms::traits::PRF;
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::{ToBytesBEGadget, ToBytesLEGadget},
    integers::uint::UInt8,
    traits::{alloc::AllocGadget, eq::EqGadget},
};

pub trait PRFGadget<P: PRF, F: Field> {
    type OutputGadget: EqGadget<F> + ToBytesBEGadget<F> + ToBytesLEGadget<F> + AllocGadget<P::Output, F> + Clone + Debug;

    fn new_seed<CS: ConstraintSystem<F>>(cs: CS, output: &P::Seed) -> Vec<UInt8>;

    fn check_evaluation_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        seed: &[UInt8],
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}
