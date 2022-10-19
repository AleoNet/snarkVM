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
    pub fn is_owner(&self, address: &Address<N>, view_key: &ViewKey<N>) -> bool {
        match &self.owner {
            // If the owner is public, check if the address is the owner.
            Owner::Public(owner) => owner == address,
            // If the owner is private, decrypt the owner to check if it matches the address.
            Owner::Private(ciphertext) => {
                // Compute the record view key.
                let record_view_key = (self.nonce * **view_key).to_x_coordinate();
                // Compute the 0th randomizer.
                let randomizer = N::hash_many_psd8(&[N::encryption_domain(), record_view_key], 1);
                // Decrypt the owner.
                match Address::from_field(&(ciphertext[0] - randomizer[0])) {
                    Ok(owner) => &owner == address,
                    Err(_) => false,
                }
            }
        }
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

    const ITERATIONS: u64 = 1_000;

    fn check_is_owner<N: Network>(
        view_key: ViewKey<N>,
        owner: Owner<N, Plaintext<N>>,
        gates: Balance<N, Plaintext<N>>,
        rng: &mut TestRng,
    ) -> Result<()> {
        // Prepare the record.
        let randomizer = Scalar::rand(rng);
        let record = Record {
            owner,
            gates,
            data: IndexMap::from_iter(
                vec![
                    (Identifier::from_str("a")?, Entry::Private(Plaintext::from(Literal::Field(Field::rand(rng))))),
                    (Identifier::from_str("b")?, Entry::Private(Plaintext::from(Literal::Scalar(Scalar::rand(rng))))),
                ]
                .into_iter(),
            ),
            nonce: N::g_scalar_multiply(&randomizer),
        };

        // Encrypt the record.
        let ciphertext = record.encrypt(randomizer)?;

        // Compute the address.
        let address = Address::try_from(&view_key)?;

        // Ensure the record belongs to the owner.
        assert!(ciphertext.is_owner(&address, &view_key));

        // Sample a random view key and address.
        let private_key = PrivateKey::<N>::new(rng)?;
        let view_key = ViewKey::try_from(&private_key)?;
        let address = Address::try_from(&private_key)?;

        // Ensure the random address is not the owner.
        assert!(!ciphertext.is_owner(&address, &view_key));

        Ok(())
    }

    #[test]
    fn test_is_owner() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a view key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng)?;
            let view_key = ViewKey::try_from(&private_key)?;
            let address = Address::try_from(&private_key)?;

            // Public owner and public gates.
            let owner = Owner::Public(address);
            let gates = Balance::Public(U64::new(u64::rand(&mut rng) >> 12));
            check_is_owner::<CurrentNetwork>(view_key, owner, gates, &mut rng)?;

            // Private owner and public gates.
            let owner = Owner::Private(Plaintext::from(Literal::Address(address)));
            let gates = Balance::Public(U64::new(u64::rand(&mut rng) >> 12));
            check_is_owner::<CurrentNetwork>(view_key, owner, gates, &mut rng)?;

            // Public owner and private gates.
            let owner = Owner::Public(address);
            let gates = Balance::Private(Plaintext::from(Literal::U64(U64::new(u64::rand(&mut rng) >> 12))));
            check_is_owner::<CurrentNetwork>(view_key, owner, gates, &mut rng)?;

            // Private owner and private gates.
            let owner = Owner::Private(Plaintext::from(Literal::Address(address)));
            let gates = Balance::Private(Plaintext::from(Literal::U64(U64::new(u64::rand(&mut rng) >> 12))));
            check_is_owner::<CurrentNetwork>(view_key, owner, gates, &mut rng)?;
        }
        Ok(())
    }
}
