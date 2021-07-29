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

use snarkvm_algorithms::traits::EncryptionScheme;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::ToBytesGadget,
    traits::{alloc::AllocGadget, eq::EqGadget},
    UInt8,
};
use snarkvm_fields::PrimeField;

pub trait EncryptionGadget<E: EncryptionScheme, F: PrimeField>: AllocGadget<E, F> + Clone {
    type PrivateKeyGadget: AllocGadget<<E as EncryptionScheme>::PrivateKey, F>
        + ToBytesGadget<F>
        + Clone
        + Sized
        + Debug;
    type PublicKeyGadget: AllocGadget<<E as EncryptionScheme>::PublicKey, F>
        + EqGadget<F>
        + ToBytesGadget<F>
        + Clone
        + Sized
        + Debug;
    type RandomnessGadget: AllocGadget<E::Randomness, F> + Clone + Sized + Debug;

    fn check_public_key_gadget<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        private_key: &Self::PrivateKeyGadget,
    ) -> Result<Self::PublicKeyGadget, SynthesisError>;

    fn check_encryption_gadget<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        randomness: &Self::RandomnessGadget,
        public_key: &Self::PublicKeyGadget,
        input: &[UInt8],
    ) -> Result<Vec<UInt8>, SynthesisError>;
}
