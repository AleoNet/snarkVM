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

impl<A: Aleo> Record<A, Plaintext<A>> {
    /// Encrypts `self` for the record owner under the given randomizer.
    pub fn encrypt(&self, randomizer: &Scalar<A>) -> Record<A, Ciphertext<A>> {
        // Compute the record view key.
        let record_view_key = ((*self.owner).to_group() * randomizer).to_x_coordinate();
        // Encrypt the record.
        self.encrypt_symmetric(record_view_key)
    }

    /// Encrypts `self` under the given record view key.
    pub fn encrypt_symmetric(&self, record_view_key: Field<A>) -> Record<A, Ciphertext<A>> {
        // Determine the number of randomizers needed to encrypt the record.
        let num_randomizers = self.num_randomizers();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), record_view_key], num_randomizers);
        // Encrypt the record.
        self.encrypt_with_randomizers(&randomizers)
    }

    /// Encrypts `self` under the given randomizers.
    fn encrypt_with_randomizers(&self, randomizers: &[Field<A>]) -> Record<A, Ciphertext<A>> {
        // Initialize an index to keep track of the randomizer index.
        let mut index: usize = 0;

        // Encrypt the owner.
        let owner = match self.owner.is_public().eject_value() {
            true => self.owner.encrypt(&[]),
            false => self.owner.encrypt(&[randomizers[index].clone()]),
        };

        // Increment the index if the owner is private.
        if owner.is_private().eject_value() {
            index += 1;
        }

        // Encrypt the gates.
        let gates = match self.gates.is_public().eject_value() {
            true => self.gates.encrypt(&[]),
            false => self.gates.encrypt(&[randomizers[index].clone()]),
        };

        // Increment the index if the gates is private.
        if gates.is_private().eject_value() {
            index += 1;
        }

        // Encrypt the data.
        let mut encrypted_data = IndexMap::with_capacity(self.data.len());
        for (id, entry, num_randomizers) in self.data.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers as usize];
            // Encrypt the entry.
            let entry = match entry {
                // Constant entries do not need to be encrypted.
                Entry::Constant(plaintext) => Entry::Constant(plaintext.clone()),
                // Public entries do not need to be encrypted.
                Entry::Public(plaintext) => Entry::Public(plaintext.clone()),
                // Private entries are encrypted with the given randomizers.
                Entry::Private(private) => Entry::Private(private.encrypt_with_randomizers(randomizers)),
            };
            // Insert the encrypted entry.
            if encrypted_data.insert(id.clone(), entry).is_some() {
                A::halt(format!("Duplicate identifier in record: {}", id))
            }
            // Increment the index.
            index += num_randomizers as usize;
        }

        // Return the encrypted record.
        Record { owner, gates, data: encrypted_data }
    }
}
