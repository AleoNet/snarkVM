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

use crate::utilities::alloc::AllocGadget;
use crate::utilities::eq::EqGadget;
use crate::utilities::uint::UInt8;
use crate::utilities::ToBytesGadget;
use snarkvm_algorithms::traits::SignatureScheme;
use snarkvm_fields::Field;
use snarkvm_r1cs::errors::SynthesisError;
use snarkvm_r1cs::ConstraintSystem;

pub trait SignaturePublicKeyRandomizationGadget<S: SignatureScheme, F: Field> {
    type ParametersGadget: AllocGadget<S::Parameters, F>;
    type PublicKeyGadget: ToBytesGadget<F> + EqGadget<F> + AllocGadget<S::PublicKey, F> + Clone;

    fn check_randomization_gadget<CS: ConstraintSystem<F>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        public_key: &Self::PublicKeyGadget,
        randomness: &[UInt8],
    ) -> Result<Self::PublicKeyGadget, SynthesisError>;
}
