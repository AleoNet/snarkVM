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

impl<N: Network> Data<N, Ciphertext<N>> {
    /// Decrypts `self` into plaintext using the given view key & nonce.
    pub fn decrypt(&self, view_key: ViewKey<N>, nonce: N::Affine) -> Result<Data<N, Plaintext<N>>> {
        // Compute the data view key.
        let data_view_key = (nonce * *view_key).to_affine().to_x_coordinate();
        // Decrypt the data.
        self.decrypt_symmetric(&data_view_key)
    }

    /// Decrypts `self` into plaintext using the given data view key.
    pub fn decrypt_symmetric(&self, data_view_key: &N::Field) -> Result<Data<N, Plaintext<N>>> {
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers =
            self.0.iter().map(|(_, value)| value.num_randomizers()).collect::<Result<Vec<_>>>()?.iter().sum();
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *data_view_key], num_randomizers);
        // Decrypt the data.
        let mut index: usize = 0;
        let mut decrypted_data = Vec::with_capacity(self.0.len());
        for (id, value, num_randomizers) in self.0.iter().map(|(id, value)| (id, value, value.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this value.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Decrypt the value, and add the value.
            decrypted_data.push((id.clone(), value.decrypt(randomizers)?));
            // Increment the index.
            index += num_randomizers;
        }
        Ok(Data(decrypted_data))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;
    use snarkvm_console_account::PrivateKey;
    use snarkvm_console_network::Testnet3;
    use snarkvm_console_types::Field;
    use snarkvm_utilities::test_crypto_rng;

    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Sample a view key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let view_key = ViewKey::try_from(&private_key)?;
            let address = Address::try_from(&private_key)?;

            let data = Data(vec![(
                Identifier::from_str("a")?,
                Value::Private(Plaintext::from(Literal::Field(Field::new(Uniform::rand(rng))))),
            )]);

            let randomizer = <CurrentNetwork as Network>::Scalar::rand(rng);
            let ciphertext = data.encrypt(address, randomizer)?;

            let nonce = <CurrentNetwork as Network>::g_scalar_multiply(&randomizer).to_affine();
            assert_eq!(data, ciphertext.decrypt(view_key, nonce)?);
        }
        Ok(())
    }
}
