// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod bytes;
mod serialize;
mod string;

use snarkvm_console_account::{Address, PrivateKey, Signature};
use snarkvm_console_network::Network;
use snarkvm_console_types::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ProgramOwner<N: Network> {
    /// The address of the program owner.
    address: Address<N>,
    /// The signature of the program owner, over the deployment transaction ID.
    signature: Signature<N>,
}

impl<N: Network> ProgramOwner<N> {
    /// Initializes a new program owner.
    pub fn new<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        transaction_id: N::TransactionID,
        rng: &mut R,
    ) -> Result<Self> {
        // Derive the address.
        let address = Address::try_from(private_key)?;
        // Sign the transaction ID.
        let signature = private_key.sign(&[*transaction_id], rng)?;
        // Return the program owner.
        Ok(Self { signature, address })
    }

    /// Initializes a new program owner from an address and signature.
    pub fn from(address: Address<N>, signature: Signature<N>) -> Self {
        Self { address, signature }
    }

    /// Returns the address of the program owner.
    pub const fn address(&self) -> Address<N> {
        self.address
    }

    /// Returns the signature of the program owner.
    pub const fn signature(&self) -> &Signature<N> {
        &self.signature
    }

    /// Verify that the signature is valid for the given transaction ID.
    pub fn verify(&self, transaction_id: N::TransactionID) -> bool {
        self.signature.verify(&self.address, &[*transaction_id])
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use snarkvm_console_network::Testnet3;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

    pub(crate) fn sample_program_owner() -> ProgramOwner<CurrentNetwork> {
        static INSTANCE: OnceCell<ProgramOwner<CurrentNetwork>> = OnceCell::new();
        *INSTANCE.get_or_init(|| {
            // Initialize the RNG.
            let rng = &mut TestRng::default();

            // Initialize a private key.
            let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

            // Initialize a transaction ID.
            let field: Field<CurrentNetwork> = rng.gen();
            let transaction_id = field.into();

            // Return the program owner.
            ProgramOwner::new(&private_key, transaction_id, rng).unwrap()
        })
    }

    #[test]
    fn test_verify_program_owner() {
        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Initialize a transaction ID.
        let field: Field<CurrentNetwork> = rng.gen();
        let transaction_id = field.into();

        // Construct the program owner.
        let owner = ProgramOwner::new(&private_key, transaction_id, rng).unwrap();
        // Ensure that the program owner is verified for the given transaction ID.
        assert!(owner.verify(transaction_id));

        // Ensure that the program owner is not verified for a different transaction ID.
        let field: Field<CurrentNetwork> = rng.gen();
        let incorrect_transaction_id = field.into();
        assert!(!owner.verify(incorrect_transaction_id));
    }
}
