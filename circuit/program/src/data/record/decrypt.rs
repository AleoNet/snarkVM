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

impl<A: Aleo> Record<A, Ciphertext<A>> {
    /// Decrypts `self` into plaintext using the given view key & nonce.
    pub fn decrypt(&self, view_key: &ViewKey<A>, nonce: &Group<A>) -> Record<A, Plaintext<A>> {
        // Compute the data view key.
        let data_view_key = (&**view_key * nonce).to_x_coordinate();
        // Decrypt the data.
        self.decrypt_symmetric(data_view_key)
    }

    // /// Decrypts `self` into plaintext using the given data view key.
    // pub fn decrypt_symmetric(&self, data_view_key: Field<A>) -> Record<A, Plaintext<A>> {
    //     // Determine the number of randomizers needed to encrypt the data.
    //     let num_randomizers = self.0.iter().map(|(_, value)| value.num_randomizers()).sum();
    //     // Prepare a randomizer for each field element.
    //     let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], num_randomizers);
    //     // Decrypt the data.
    //     let mut index: usize = 0;
    //     let mut decrypted_data = IndexMap::with_capacity(self.0.len());
    //     for (id, value, num_randomizers) in self.0.iter().map(|(id, value)| (id, value, value.num_randomizers())) {
    //         // Retrieve the randomizers for this value.
    //         let randomizers = &randomizers[index..index + num_randomizers as usize];
    //         // Decrypt the value, and add the value.
    //         decrypted_data.insert(id.clone(), value.decrypt(randomizers));
    //         // Increment the index.
    //         index += num_randomizers as usize;
    //     }
    //     Record(decrypted_data)
    // }

    /// Decrypts `self` into plaintext using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: Field<A>) -> Record<A, Plaintext<A>> {
        // Determine the number of randomizers needed to encrypt the record.
        let num_randomizers = self.num_randomizers();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), record_view_key], num_randomizers);
        // Decrypt the record.
        self.decrypt_with_randomizers(&randomizers)
    }

    /// Decrypts `self` into plaintext using the given randomizers.
    fn decrypt_with_randomizers(&self, randomizers: &[Field<A>]) -> Record<A, Plaintext<A>> {
        // Initialize an index to keep track of the randomizer index.
        let mut index: usize = 0;

        // Decrypt the owner.
        let owner = match self.owner.is_public().eject_value() {
            true => self.owner.decrypt(&[]),
            false => self.owner.decrypt(&[randomizers[index].clone()]),
        };

        // Increment the index if the owner is private.
        if owner.is_private().eject_value() {
            index += 1;
        }

        // Decrypt the balance.
        let balance = match self.balance.is_public().eject_value() {
            true => self.balance.decrypt(&[]),
            false => self.balance.decrypt(&[randomizers[index].clone()]),
        };

        // Increment the index if the balance is private.
        if balance.is_private().eject_value() {
            index += 1;
        }

        // Decrypt the program data.
        let mut decrypted_data = IndexMap::with_capacity(self.data.len());
        for (id, entry, num_randomizers) in self.data.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers as usize];
            // Decrypt the entry.
            let entry = match entry {
                // Constant entries do not need to be decrypted.
                Entry::Constant(plaintext) => Entry::Constant(plaintext.clone()),
                // Public entries do not need to be decrypted.
                Entry::Public(plaintext) => Entry::Public(plaintext.clone()),
                // Private entries are decrypted with the given randomizers.
                Entry::Private(private) => Entry::Private(Plaintext::from_fields(
                    &private
                        .iter()
                        .zip_eq(randomizers)
                        .map(|(ciphertext, randomizer)| ciphertext - randomizer)
                        .collect::<Vec<_>>(),
                )),
            };
            // Insert the decrypted entry.
            if decrypted_data.insert(id.clone(), entry).is_some() {
                A::halt(format!("Duplicate identifier in record: {}", id))
            }
            // Increment the index.
            index += num_randomizers as usize;
        }

        // Return the decrypted record.
        Record { owner, balance, data: decrypted_data }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{Circuit, Literal};
    use snarkvm_circuit_types::Field;
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Generate a private key, view key, and address.
            let private_key = snarkvm_console_account::PrivateKey::<<Circuit as Environment>::Network>::new(rng)?;
            let view_key = snarkvm_console_account::ViewKey::try_from(private_key)?;
            let address = snarkvm_console_account::Address::try_from(private_key)?;

            // Initialize a view key and address.
            let view_key = ViewKey::<Circuit>::new(Mode::Private, view_key);
            let address = Address::<Circuit>::new(Mode::Private, address);

            let record = Record(vec![(
                Identifier::from_str("a")?,
                Value::Private(Plaintext::from(Literal::Field(Field::new(Mode::Private, Uniform::rand(rng))))),
            )]);

            let randomizer = Scalar::new(Mode::Private, Uniform::rand(rng));
            let ciphertext = record.encrypt(&address, &randomizer);

            let nonce = <Circuit as Aleo>::g_scalar_multiply(&randomizer);
            assert_eq!(record.eject(), ciphertext.decrypt(&view_key, &nonce).eject());
        }
        Ok(())
    }

    #[test]
    fn test_encrypt_symmetric_and_decrypt_symmetric() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Sample a random symmetric key and data.
            let symmetric_key = Field::<Circuit>::new(Mode::Private, Uniform::rand(rng));
            let record = Record(vec![(
                Identifier::from_str("a")?,
                Value::Private(Plaintext::from(Literal::Field(Field::new(Mode::Private, Uniform::rand(rng))))),
            )]);

            let ciphertext = record.encrypt_symmetric(symmetric_key.clone());
            assert_eq!(record.eject(), ciphertext.decrypt_symmetric(symmetric_key).eject());
        }
        Ok(())
    }
}
