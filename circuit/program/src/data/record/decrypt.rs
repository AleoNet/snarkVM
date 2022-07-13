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
    /// Decrypts `self` into a plaintext record using the given view key & nonce.
    pub fn decrypt(&self, view_key: &ViewKey<A>, nonce: &Group<A>) -> Record<A, Plaintext<A>> {
        // Compute the record view key.
        let record_view_key = (&**view_key * nonce).to_x_coordinate();
        // Decrypt the record.
        self.decrypt_symmetric(record_view_key)
    }

    /// Decrypts `self` into a plaintext record using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: Field<A>) -> Record<A, Plaintext<A>> {
        // Determine the number of randomizers needed to encrypt the record.
        let num_randomizers = self.num_randomizers();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), record_view_key], num_randomizers);
        // Decrypt the record.
        self.decrypt_with_randomizers(&randomizers)
    }

    /// Decrypts `self` into a plaintext record using the given randomizers.
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
                Entry::Private(private) => Entry::Private(private.decrypt_with_randomizers(randomizers)),
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
    use snarkvm_circuit_types::{Address, Field, U64};
    use snarkvm_utilities::{test_crypto_rng, test_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_encrypt_and_decrypt<A: Aleo>(
        view_key: &ViewKey<A>,
        owner: Owner<A, Plaintext<A>>,
        balance: Balance<A, Plaintext<A>>,
    ) -> Result<()> {
        // Prepare the record.
        let record = Record {
            owner,
            balance,
            data: IndexMap::from_iter(
                vec![
                    (
                        Identifier::from_str("a")?,
                        Entry::Private(Plaintext::from(Literal::Field(Field::new(
                            Mode::Private,
                            Uniform::rand(&mut test_rng()),
                        )))),
                    ),
                    (
                        Identifier::from_str("b")?,
                        Entry::Private(Plaintext::from(Literal::Scalar(Scalar::new(
                            Mode::Private,
                            Uniform::rand(&mut test_rng()),
                        )))),
                    ),
                ]
                .into_iter(),
            ),
        };

        // Encrypt the record.
        let randomizer = Scalar::new(Mode::Private, Uniform::rand(&mut test_rng()));
        let ciphertext = record.encrypt(&randomizer);
        // Decrypt the record.
        let nonce = A::g_scalar_multiply(&randomizer);
        assert_eq!(record.eject(), ciphertext.decrypt(view_key, &nonce).eject());
        Ok(())
    }

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
            let owner = address;

            // Public owner and public balance.
            {
                let owner = Owner::Public(Address::<Circuit>::new(Mode::Public, owner));
                let balance =
                    Balance::Public(U64::new(Mode::Public, console::U64::new(u64::rand(&mut test_rng()) >> 12)));
                check_encrypt_and_decrypt::<Circuit>(&view_key, owner, balance)?;
            }

            // Private owner and public balance.
            {
                let owner =
                    Owner::Private(Plaintext::from(Literal::Address(Address::<Circuit>::new(Mode::Private, owner))));
                let balance =
                    Balance::Public(U64::new(Mode::Public, console::U64::new(u64::rand(&mut test_rng()) >> 12)));
                check_encrypt_and_decrypt::<Circuit>(&view_key, owner, balance)?;
            }

            // Public owner and private balance.
            {
                let owner = Owner::Public(Address::<Circuit>::new(Mode::Public, owner));
                let balance = Balance::Private(Plaintext::from(Literal::U64(U64::new(
                    Mode::Private,
                    console::U64::new(u64::rand(&mut test_rng()) >> 12),
                ))));
                check_encrypt_and_decrypt::<Circuit>(&view_key, owner, balance)?;
            }

            // Private owner and private balance.
            {
                let owner =
                    Owner::Private(Plaintext::from(Literal::Address(Address::<Circuit>::new(Mode::Private, owner))));
                let balance = Balance::Private(Plaintext::from(Literal::U64(U64::new(
                    Mode::Private,
                    console::U64::new(u64::rand(&mut test_rng()) >> 12),
                ))));
                check_encrypt_and_decrypt::<Circuit>(&view_key, owner, balance)?;
            }
        }
        Ok(())
    }
}
