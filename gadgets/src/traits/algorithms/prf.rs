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

use crate::algorithms::PRF;
use crate::curves::Field;
use crate::gadgets::r1cs::ConstraintSystem;
use crate::gadgets::utilities::alloc::AllocGadget;
use crate::gadgets::utilities::eq::EqGadget;
use crate::gadgets::utilities::uint::UInt8;
use crate::gadgets::utilities::ToBytesGadget;
use snarkvm_gadgets::errors::SynthesisError;

use std::fmt::Debug;

pub trait PRFGadget<P: PRF, F: Field> {
    type OutputGadget: EqGadget<F> + ToBytesGadget<F> + AllocGadget<P::Output, F> + Clone + Debug;

    fn new_seed<CS: ConstraintSystem<F>>(cs: CS, output: &P::Seed) -> Vec<UInt8>;

    fn check_evaluation_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        seed: &[UInt8],
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}
