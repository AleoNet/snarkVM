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

use snarkvm_algorithms::traits::SignatureScheme;
use snarkvm_fields::Field;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::ToBytesGadget,
    traits::{alloc::AllocGadget, eq::EqGadget},
    Boolean,
    ToBitsLEGadget,
};

pub trait SignatureGadget<S: SignatureScheme, F: Field>: AllocGadget<S, F> {
    type ComputeKeyGadget: ToBitsLEGadget<F> + Clone;
    type PublicKeyGadget: ToBytesGadget<F> + EqGadget<F> + AllocGadget<S::PublicKey, F> + Clone;
    type SignatureGadget: ToBytesGadget<F> + EqGadget<F> + AllocGadget<S::Signature, F> + Clone;

    fn compute_key<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        signature: &Self::SignatureGadget,
    ) -> Result<Self::ComputeKeyGadget, SynthesisError>;

    fn verify<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        public_key: &Self::PublicKeyGadget,
        message: &[Boolean],
        signature: &Self::SignatureGadget,
    ) -> Result<Boolean, SynthesisError>;
}
