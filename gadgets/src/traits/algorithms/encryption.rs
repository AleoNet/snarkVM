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

use std::fmt::Debug;

use snarkvm_algorithms::traits::EncryptionScheme;
use snarkvm_r1cs::{errors::SynthesisError, ConstraintSystem};

use crate::{
    bits::ToBytesGadget,
    traits::{alloc::AllocGadget, eq::EqGadget},
    FpGadget,
    UInt8,
};
use snarkvm_fields::PrimeField;

pub trait EncryptionGadget<E: EncryptionScheme, F: PrimeField>: AllocGadget<E, F> + Clone {
    type CiphertextRandomizer: AllocGadget<<E as EncryptionScheme>::CiphertextRandomizer, F>
        + EqGadget<F>
        + ToBytesGadget<F>
        + Clone
        + Sized
        + Debug;
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
    type ScalarRandomnessGadget: AllocGadget<E::ScalarRandomness, F> + Clone + Sized + Debug;
    type SymmetricKeyGadget: AllocGadget<<E as EncryptionScheme>::SymmetricKey, F>
        + ToBytesGadget<F>
        + Clone
        + Sized
        + Debug;
    type SymmetricKeyCommitmentGadget: AllocGadget<<E as EncryptionScheme>::SymmetricKey, F>
        + ToBytesGadget<F>
        + Clone
        + Sized
        + Debug;

    fn check_public_key_gadget<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        private_key: &Self::PrivateKeyGadget,
    ) -> Result<Self::PublicKeyGadget, SynthesisError>;

    fn encode_message<CS: ConstraintSystem<F>>(cs: CS, message: &[UInt8]) -> Result<Vec<FpGadget<F>>, SynthesisError>;

    fn check_symmetric_key_commitment<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        symmetric_key: &Self::SymmetricKeyGadget,
    ) -> Result<Self::SymmetricKeyCommitmentGadget, SynthesisError>;

    fn check_encryption_from_scalar_randomness<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        randomness: &Self::ScalarRandomnessGadget,
        public_key: &Self::PublicKeyGadget,
        encoded_message: &[FpGadget<F>],
    ) -> Result<(Self::CiphertextRandomizer, Vec<FpGadget<F>>, Self::SymmetricKeyGadget), SynthesisError>;

    /// Assumes symmetric key is committed before hand.
    /// Otherwise, this allows the decrypter to open the ciphertext to any
    /// plaintext.
    ///
    /// # Returns
    /// The ciphertext produced by this key.
    fn check_encryption_from_symmetric_key<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        symmetric_key: &Self::SymmetricKeyGadget,
        plaintext: &[FpGadget<F>],
    ) -> Result<Vec<FpGadget<F>>, SynthesisError>;

    fn check_encryption_from_ciphertext_randomizer<CS: ConstraintSystem<F>>(
        &self,
        cs: CS,
        ciphertext_randomizer: &Self::CiphertextRandomizer,
        private_key: &Self::PrivateKeyGadget,
        encoded_message: &[FpGadget<F>],
    ) -> Result<Vec<FpGadget<F>>, SynthesisError>;
}
