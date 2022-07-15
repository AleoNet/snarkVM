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

impl<N: Network> Record<N, Ciphertext<N>> {
    /// Decrypts `self` into plaintext using the given view key & nonce.
    pub fn decrypt(&self, view_key: ViewKey<N>, nonce: Group<N>) -> Result<Record<N, Plaintext<N>>> {
        // Compute the record view key.
        let record_view_key = (nonce * *view_key).to_x_coordinate();
        // Decrypt the record.
        self.decrypt_symmetric(&record_view_key)
    }

    /// Decrypts `self` into plaintext using the given record view key.
    pub fn decrypt_symmetric(&self, record_view_key: &Field<N>) -> Result<Record<N, Plaintext<N>>> {
        // Determine the number of randomizers needed to encrypt the record.
        let num_randomizers = self.num_randomizers()?;
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *record_view_key], num_randomizers);
        // Decrypt the record.
        self.decrypt_with_randomizers(&randomizers)
    }

    /// Decrypts `self` into plaintext using the given randomizers.
    fn decrypt_with_randomizers(&self, randomizers: &[Field<N>]) -> Result<Record<N, Plaintext<N>>> {
        // Initialize an index to keep track of the randomizer index.
        let mut index: usize = 0;

        // Decrypt the owner.
        let owner = match self.owner.is_public() {
            true => self.owner.decrypt(&[])?,
            false => self.owner.decrypt(&[randomizers[index]])?,
        };

        // Increment the index if the owner is private.
        if owner.is_private() {
            index += 1;
        }

        // Decrypt the gates.
        let gates = match self.gates.is_public() {
            true => self.gates.decrypt(&[])?,
            false => self.gates.decrypt(&[randomizers[index]])?,
        };

        // Increment the index if the gates is private.
        if gates.is_private() {
            index += 1;
        }

        // Decrypt the program data.
        let mut decrypted_data = IndexMap::with_capacity(self.data.len());
        for (id, entry, num_randomizers) in self.data.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers];
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
                        .map(|(ciphertext, randomizer)| *ciphertext - randomizer)
                        .collect::<Vec<_>>(),
                )?),
            };
            // Insert the decrypted entry.
            if decrypted_data.insert(*id, entry).is_some() {
                bail!("Duplicate identifier in record: {}", id);
            }
            // Increment the index.
            index += num_randomizers;
        }

        // Return the decrypted record.
        Ok(Record { owner, gates, data: decrypted_data })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;
    use snarkvm_console_account::PrivateKey;
    use snarkvm_console_network::Testnet3;
    use snarkvm_console_types::Field;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    fn check_encrypt_and_decrypt<N: Network>(
        view_key: ViewKey<N>,
        owner: Owner<N, Plaintext<N>>,
        gates: Balance<N, Plaintext<N>>,
    ) -> Result<()> {
        // Prepare the record.
        let record = Record {
            owner,
            gates,
            data: IndexMap::from_iter(
                vec![
                    (
                        Identifier::from_str("a")?,
                        Entry::Private(Plaintext::from(Literal::Field(Field::rand(&mut test_rng())))),
                    ),
                    (
                        Identifier::from_str("b")?,
                        Entry::Private(Plaintext::from(Literal::Scalar(Scalar::rand(&mut test_rng())))),
                    ),
                ]
                .into_iter(),
            ),
        };
        // Encrypt the record.
        let randomizer = Scalar::rand(&mut test_rng());
        let ciphertext = record.encrypt(randomizer)?;
        // Decrypt the record.
        let nonce = N::g_scalar_multiply(&randomizer);
        assert_eq!(record, ciphertext.decrypt(view_key, nonce)?);
        Ok(())
    }

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a view key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let view_key = ViewKey::try_from(&private_key)?;
            let address = Address::try_from(&private_key)?;

            // Public owner and public gates.
            let owner = Owner::Public(address);
            let gates = Balance::Public(U64::new(u64::rand(&mut test_rng()) >> 12));
            check_encrypt_and_decrypt::<CurrentNetwork>(view_key, owner, gates)?;

            // Private owner and public gates.
            let owner = Owner::Private(Plaintext::from(Literal::Address(address)));
            let gates = Balance::Public(U64::new(u64::rand(&mut test_rng()) >> 12));
            check_encrypt_and_decrypt::<CurrentNetwork>(view_key, owner, gates)?;

            // Public owner and private gates.
            let owner = Owner::Public(address);
            let gates = Balance::Private(Plaintext::from(Literal::U64(U64::new(u64::rand(&mut test_rng()) >> 12))));
            check_encrypt_and_decrypt::<CurrentNetwork>(view_key, owner, gates)?;

            // Private owner and private gates.
            let owner = Owner::Private(Plaintext::from(Literal::Address(address)));
            let gates = Balance::Private(Plaintext::from(Literal::U64(U64::new(u64::rand(&mut test_rng()) >> 12))));
            check_encrypt_and_decrypt::<CurrentNetwork>(view_key, owner, gates)?;
        }
        Ok(())
    }
}
