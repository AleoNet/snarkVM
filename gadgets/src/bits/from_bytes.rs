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

use crate::UInt8;
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

pub trait FromBytesBEGadget<F: Field, const SIZE_BYTES: usize> {
    fn from_bytes_be<CS: ConstraintSystem<F>>(bytes: [UInt8; SIZE_BYTES], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bytes_be_strict<CS: ConstraintSystem<F>>(
        bytes: [UInt8; SIZE_BYTES],
        cs: CS,
    ) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}

pub trait FromBytesLEGadget<F: Field, const SIZE_BYTES: usize> {
    fn from_bytes_le<CS: ConstraintSystem<F>>(bytes: [UInt8; SIZE_BYTES], cs: CS) -> Result<Self, SynthesisError>
    where
        Self: Sized;

    fn from_bytes_le_strict<CS: ConstraintSystem<F>>(
        bytes: [UInt8; SIZE_BYTES],
        cs: CS,
    ) -> Result<Self, SynthesisError>
    where
        Self: Sized;
}
