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

use snarkvm_utilities::{rand::Uniform, FromBytes, ToBits, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{fmt::Debug, hash::Hash};

pub trait EncryptionScheme: Sized + Debug + Clone + PartialEq + Eq {
    type CiphertextRandomizer: Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + ToBits;
    type MessageType: Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + ToBits;
    type Parameters: Clone + Debug + Eq;
    type PrivateKey: Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + ToBits + Uniform;
    type PublicKey: Copy + Clone + Debug + Default + Eq + ToBytes + FromBytes;
    type ScalarRandomness: Copy + Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + Uniform + Sync;
    type SymmetricKey: Copy + Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + Send + Sync;
    type SymmetricKeyCommitment: Copy + Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + Send + Sync;

    fn setup(message: &str) -> Self;

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Self::PrivateKey;

    fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Self::PublicKey;

    fn generate_asymmetric_key<R: Rng + CryptoRng>(
        &self,
        public_key: &Self::PublicKey,
        rng: &mut R,
    ) -> (Self::ScalarRandomness, Self::CiphertextRandomizer, Self::SymmetricKey);

    fn generate_symmetric_key(
        &self,
        private_key: &Self::PrivateKey,
        ciphertext_randomizer: Self::CiphertextRandomizer,
    ) -> Option<Self::SymmetricKey>;

    fn generate_symmetric_key_commitment(&self, symmetric_key: &Self::SymmetricKey) -> Self::SymmetricKeyCommitment;

    fn encode_message(message: &[u8]) -> Result<Vec<Self::MessageType>>;

    fn decode_message(encoded_message: &[Self::MessageType]) -> Result<Vec<u8>>;

    fn encrypt(&self, symmetric_key: &Self::SymmetricKey, message: &[Self::MessageType]) -> Vec<Self::MessageType>;

    fn decrypt(&self, symmetric_key: &Self::SymmetricKey, ciphertext: &[Self::MessageType]) -> Vec<Self::MessageType>;

    fn parameters(&self) -> &<Self as EncryptionScheme>::Parameters;
}
