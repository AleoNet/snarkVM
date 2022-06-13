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

impl<N: Network> Record<N, Plaintext<N>> {
    /// Encrypts `self` under the given Aleo address and randomizer.
    pub fn encrypt(&self, address: Address<N>, randomizer: Scalar<N>) -> Result<Record<N, Ciphertext<N>>> {
        // Compute the data view key.
        let data_view_key = (*address * randomizer).to_x_coordinate();
        // Encrypt the data.
        self.encrypt_symmetric(&data_view_key)
    }

    /// Encrypts `self` under the given data view key.
    pub fn encrypt_symmetric(&self, data_view_key: &Field<N>) -> Result<Record<N, Ciphertext<N>>> {
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers = self.num_randomizers()?;
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *data_view_key], num_randomizers);
        // Encrypt the data.
        self.encrypt_with_randomizers(&randomizers)
    }

    /// Encrypts `self` under the given randomizers.
    fn encrypt_with_randomizers(&self, randomizers: &[Field<N>]) -> Result<Record<N, Ciphertext<N>>> {
        // Initialize an index to keep track of the randomizer index.
        let mut index: usize = 0;

        // Encrypt the owner.
        let owner = match self.owner.is_public() {
            true => self.owner.encrypt(&[])?,
            false => self.owner.encrypt(&[randomizers[index]])?,
        };

        // Increment the index if the owner is private.
        if owner.is_private() {
            index += 1;
        }

        // Encrypt the balance.
        let balance = match self.balance.is_public() {
            true => self.balance.encrypt(&[])?,
            false => self.balance.encrypt(&[randomizers[index]])?,
        };

        // Increment the index if the balance is private.
        if balance.is_private() {
            index += 1;
        }

        // Encrypt the data.
        let mut encrypted_data = IndexMap::with_capacity(self.data.len());
        for (id, value, num_randomizers) in self.data.iter().map(|(id, value)| (id, value, value.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this value.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Encrypt the value.
            let value = match value {
                // Constant values do not need to be encrypted.
                Value::Constant(plaintext) => Value::Constant(plaintext.clone()),
                // Public values do not need to be encrypted.
                Value::Public(plaintext) => Value::Public(plaintext.clone()),
                // Private values are encrypted with the given randomizers.
                Value::Private(private) => Value::Private(Ciphertext::try_from(
                    private
                        .to_fields()?
                        .iter()
                        .zip_eq(randomizers)
                        .map(|(plaintext, randomizer)| *plaintext + randomizer)
                        .collect::<Vec<_>>(),
                )?),
                // Record values recursively encrypt their fields.
                Value::Record(record) => Value::Record(record.encrypt_with_randomizers(randomizers)?),
            };
            // Insert the encrypted value.
            if encrypted_data.insert(id.clone(), value).is_some() {
                bail!("Duplicate identifier in record: {}", id);
            }
            // Increment the index.
            index += num_randomizers;
        }

        // Return the encrypted record.
        Ok(Record { owner, balance, data: encrypted_data })
    }
}
