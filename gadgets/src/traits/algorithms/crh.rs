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

use snarkvm_algorithms::traits::CRH;
use snarkvm_fields::{Field, PrimeField};
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::{ToBytesBEGadget, ToBytesLEGadget},
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        eq::{ConditionalEqGadget, EqGadget},
        select::CondSelectGadget,
    },
};

pub trait CRHGadget<H: CRH, F: Field>: Sized + Clone {
    type ParametersGadget: AllocGadget<H::Parameters, F> + Clone;
    type OutputGadget: ConditionalEqGadget<F>
        + EqGadget<F>
        + ToBytesBEGadget<F>
        + ToBytesLEGadget<F>
        + CondSelectGadget<F>
        + AllocGadget<H::Output, F>
        + Debug
        + Clone
        + Sized;

    fn check_evaluation_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: Vec<UInt8>,
    ) -> Result<Self::OutputGadget, SynthesisError>;
}

pub trait MaskedCRHGadget<H: CRH, F: PrimeField>: CRHGadget<H, F> {
    /// Extends the mask such that 0 => 01, 1 => 10.
    fn extend_mask<CS: ConstraintSystem<F>>(_: CS, mask: &[UInt8]) -> Result<Vec<UInt8>, SynthesisError> {
        let extended_mask = mask
            .iter()
            .flat_map(|m| {
                m.u8_to_bits_le()
                    .chunks(4)
                    .map(|c| {
                        let new_byte = c.iter().flat_map(|b| vec![*b, b.not()]).collect::<Vec<_>>();
                        UInt8::u8_from_bits_le(&new_byte)
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        Ok(extended_mask)
    }

    fn check_evaluation_gadget_masked<CS: ConstraintSystem<F>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: Vec<UInt8>,
        mask_parameters: &Self::ParametersGadget,
        mask: Vec<UInt8>,
    ) -> Result<Self::OutputGadget, SynthesisError>;
}
