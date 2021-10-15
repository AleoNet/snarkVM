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

use crate::EncryptionError;
use snarkvm_utilities::{rand::UniformRand, FromBytes, ToBits, ToBytes};

use rand::{CryptoRng, Rng};
use std::{fmt::Debug, hash::Hash};

pub trait EncryptionScheme:
    Sized + ToBytes + FromBytes + Debug + Clone + Eq + From<<Self as EncryptionScheme>::Parameters>
{
    type Parameters: Clone + Debug + Eq;
    type PrivateKey: Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + ToBits + UniformRand;
    type PublicKey: Copy + Clone + Debug + Default + Eq + ToBytes + FromBytes;
    type Randomness: Copy + Clone + Debug + Default + Eq + Hash + ToBytes + FromBytes + UniformRand;

    fn setup(message: &str) -> Self;

    fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> <Self as EncryptionScheme>::PrivateKey;

    fn generate_public_key(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
    ) -> <Self as EncryptionScheme>::PublicKey;

    fn generate_randomness<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Self::Randomness, EncryptionError>;

    fn encrypt(
        &self,
        public_key: &<Self as EncryptionScheme>::PublicKey,
        randomness: &Self::Randomness,
        message: &[u8],
    ) -> Result<Vec<u8>, EncryptionError>;

    fn decrypt(
        &self,
        private_key: &<Self as EncryptionScheme>::PrivateKey,
        ciphertext: &[u8],
    ) -> Result<Vec<u8>, EncryptionError>;

    fn parameters(&self) -> &<Self as EncryptionScheme>::Parameters;

    fn private_key_size_in_bits() -> usize;
}
