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

impl<N: Network> Ciphertext<N> {
    /// Decrypts `self` into plaintext using the given account view key & nonce.
    pub fn decrypt(&self, view_key: ViewKey<N>, nonce: Group<N>) -> Result<Plaintext<N>> {
        // Compute the plaintext view key.
        let plaintext_view_key = (nonce * *view_key).to_x_coordinate();
        // Decrypt the record.
        self.decrypt_symmetric(plaintext_view_key)
    }

    /// Decrypts `self` into plaintext using the given plaintext view key.
    pub fn decrypt_symmetric(&self, plaintext_view_key: Field<N>) -> Result<Plaintext<N>> {
        // Determine the number of randomizers needed to encrypt the plaintext.
        let num_randomizers = self.num_randomizers()?;
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), plaintext_view_key], num_randomizers);
        // Decrypt the plaintext.
        self.decrypt_with_randomizers(&randomizers)
    }

    /// Decrypts `self` into plaintext using the given randomizers.
    pub(crate) fn decrypt_with_randomizers(&self, randomizers: &[Field<N>]) -> Result<Plaintext<N>> {
        // Decrypt the ciphertext.
        Plaintext::from_fields(
            &self
                .iter()
                .zip_eq(randomizers)
                .map(|(ciphertext, randomizer)| *ciphertext - randomizer)
                .collect::<Vec<_>>(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;
    use snarkvm_console_account::{Address, PrivateKey};
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    fn check_encrypt_and_decrypt<N: Network>() -> Result<()> {
        // Prepare the plaintext.
        let plaintext_string = r"{
  foo: 5u8,
  bar: {
    baz: 10field,
    qux: {
      quux: {
        corge: {
          grault: {
            garply: {
              waldo: {
                fred: {
                  plugh: {
                    xyzzy: {
                      thud: true
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}";
        let plaintext = Plaintext::<N>::from_str(plaintext_string)?;

        // Sample a random address.
        let private_key = PrivateKey::<N>::new(&mut test_crypto_rng())?;
        let view_key = ViewKey::<N>::try_from(private_key)?;
        let address = Address::<N>::try_from(view_key)?;

        // Encrypt the plaintext.
        let randomizer = Uniform::rand(&mut test_rng());
        let ciphertext = plaintext.encrypt(&address, randomizer)?;

        // Decrypt the plaintext.
        let nonce = N::g_scalar_multiply(&randomizer);
        assert_eq!(plaintext, ciphertext.decrypt(view_key, nonce)?);
        Ok(())
    }

    fn check_encrypt_and_decrypt_symmetric<N: Network>() -> Result<()> {
        // Prepare the plaintext.
        let plaintext = Plaintext::<N>::from(Literal::Field(Uniform::rand(&mut test_rng())));

        // Encrypt the plaintext.
        let plaintext_view_key = Uniform::rand(&mut test_rng());
        let ciphertext = plaintext.encrypt_symmetric(plaintext_view_key)?;
        // Decrypt the plaintext.
        assert_eq!(plaintext, ciphertext.decrypt_symmetric(plaintext_view_key)?);
        Ok(())
    }

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        for _ in 0..ITERATIONS {
            check_encrypt_and_decrypt::<CurrentNetwork>()?;
            check_encrypt_and_decrypt_symmetric::<CurrentNetwork>()?;
        }
        Ok(())
    }
}
