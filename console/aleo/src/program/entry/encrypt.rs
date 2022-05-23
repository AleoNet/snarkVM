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

use super::*;

impl<N: Network> Entry<N, Plaintext<N>> {
    /// Returns the number of field elements to encode `self`.
    pub(crate) fn num_randomizers(&self) -> usize {
        match self {
            // Constant and public entries do not need to be encrypted.
            Self::Constant(..) | Self::Public(..) => 0,
            // Private entries need one randomizer per field element.
            Self::Private(private) => private.size_in_fields(),
        }
    }

    /// Encrypts the entry using the given randomizers.
    pub(crate) fn encrypt(&self, randomizers: &[N::Field]) -> Result<Entry<N, Ciphertext<N>>> {
        // Ensure that the number of randomizers is correct.
        if randomizers.len() != self.num_randomizers() {
            bail!(
                "Failed to encrypt: expected {} randomizers, found {} randomizers",
                randomizers.len(),
                self.num_randomizers()
            )
        }
        match self {
            // Constant entries do not need to be encrypted.
            Self::Constant(plaintext) => Ok(Entry::Constant(plaintext.clone())),
            // Public entries do not need to be encrypted.
            Self::Public(plaintext) => Ok(Entry::Public(plaintext.clone())),
            // Private entries are encrypted with the given randomizers.
            Self::Private(private) => Ok(Entry::Private(Ciphertext(
                private
                    .to_fields()?
                    .iter()
                    .zip_eq(randomizers)
                    .map(|(plaintext, randomizer)| *plaintext + randomizer)
                    .collect(),
            ))),
        }
    }
}

impl<N: Network> Entry<N, Ciphertext<N>> {
    /// Returns the number of field elements to encode `self`.
    pub(crate) fn num_randomizers(&self) -> usize {
        match self {
            // Constant and public entries do not need to be encrypted.
            Self::Constant(..) | Self::Public(..) => 0,
            // Private entries need one randomizer per field element.
            Self::Private(private) => private.size_in_fields(),
        }
    }

    /// Decrypts the entry using the given randomizers.
    pub(crate) fn decrypt(&self, randomizers: &[N::Field]) -> Result<Entry<N, Plaintext<N>>> {
        // Ensure that the number of randomizers is correct.
        if randomizers.len() != self.num_randomizers() {
            bail!(
                "Failed to decrypt: expected {} randomizers, found {} randomizers",
                randomizers.len(),
                self.num_randomizers()
            )
        }
        match self {
            // Constant entries do not need to be decrypted.
            Self::Constant(plaintext) => Ok(Entry::Constant(plaintext.clone())),
            // Public entries do not need to be decrypted.
            Self::Public(plaintext) => Ok(Entry::Public(plaintext.clone())),
            // Private entries are decrypted with the given randomizers.
            Self::Private(private) => Ok(Entry::Private(Plaintext::from_fields(
                &*private
                    .iter()
                    .zip_eq(randomizers)
                    .map(|(ciphertext, randomizer)| *ciphertext - randomizer)
                    .collect::<Vec<_>>(),
            )?)),
        }
    }
}
