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

impl<A: Aleo> Ciphertext<A> {
    /// Decrypts `self` into plaintext using the given plaintext view key.
    pub fn decrypt_symmetric(&self, plaintext_view_key: Field<A>) -> Plaintext<A> {
        // Determine the number of randomizers needed to encrypt the plaintext.
        let num_randomizers = self.num_randomizers();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), plaintext_view_key], num_randomizers);
        // Decrypt the plaintext.
        self.decrypt_with_randomizers(&randomizers)
    }

    /// Decrypts `self` into plaintext using the given randomizers.
    pub(crate) fn decrypt_with_randomizers(&self, randomizers: &[Field<A>]) -> Plaintext<A> {
        // Decrypt the ciphertext.
        Plaintext::from_fields(
            &self
                .iter()
                .zip_eq(randomizers)
                .map(|(ciphertext, randomizer)| ciphertext - randomizer)
                .collect::<Vec<_>>(),
        )
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{Circuit, Literal};
    use snarkvm_circuit_types::Field;
    use snarkvm_utilities::{test_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_encrypt_and_decrypt<A: Aleo>() -> Result<()> {
        // Prepare the plaintext.
        let plaintext = Plaintext::<A>::from(Literal::Field(Field::new(Mode::Private, Uniform::rand(&mut test_rng()))));

        // Encrypt the plaintext.
        let plaintext_view_key = Field::new(Mode::Private, Uniform::rand(&mut test_rng()));
        let ciphertext = plaintext.encrypt_symmetric(plaintext_view_key.clone());
        // Decrypt the plaintext.
        assert_eq!(plaintext.eject(), ciphertext.decrypt_symmetric(plaintext_view_key).eject());
        Ok(())
    }

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        for _ in 0..ITERATIONS {
            check_encrypt_and_decrypt::<Circuit>()?;
        }
        Ok(())
    }
}
