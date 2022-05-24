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

impl<A: Aleo> Entry<A, Plaintext<A>> {
    /// Encrypts the entry using the given randomizers.
    pub(crate) fn encrypt(&self, randomizers: &[Field<A>]) -> Entry<A, Ciphertext<A>> {
        // Ensure that the number of randomizers is correct.
        if randomizers.len() != self.num_randomizers() as usize {
            A::halt(format!(
                "Failed to encrypt: expected {} randomizers, found {} randomizers",
                randomizers.len(),
                self.num_randomizers()
            ))
        }
        match self {
            // Constant entries do not need to be encrypted.
            Self::Constant(plaintext) => Entry::Constant(plaintext.clone()),
            // Public entries do not need to be encrypted.
            Self::Public(plaintext) => Entry::Public(plaintext.clone()),
            // Private entries are encrypted with the given randomizers.
            Self::Private(private) => Entry::Private(Ciphertext(
                private
                    .to_fields()
                    .iter()
                    .zip_eq(randomizers)
                    .map(|(plaintext, randomizer)| plaintext + randomizer)
                    .collect(),
            )),
        }
    }
}
