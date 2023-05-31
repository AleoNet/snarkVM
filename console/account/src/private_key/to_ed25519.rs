// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use ed25519_dalek::{PublicKey, SecretKey};

pub const ACCOUNT_ED25519_DOMAIN: &str = "AleoAccountEd25519_0";

impl<N: Network> PrivateKey<N> {
    /// Returns the Ed25519 private key for this account private key.
    pub fn to_ed25519(&self, counter: u32) -> Result<ed25519_dalek::Keypair> {
        // Prepare the domain separator.
        let domain = Field::new_domain_separator(ACCOUNT_ED25519_DOMAIN);
        // Prepare the counter.
        let counter = Field::from_u32(counter);
        // Construct the preimage.
        let preimage = [domain, self.sk_sig.to_field()?, self.r_sig.to_field()?, counter];
        // Hash the preimage.
        let hash = N::hash_psd4(&preimage)?;
        // Construct the ed25519 secret key.
        let secret_key = SecretKey::from_bytes(&hash.to_bytes_le()?)?;
        // Construct the ed25519 public key.
        let public_key = PublicKey::from(&secret_key);
        // Construct the ed25519 keypair.
        Ok(ed25519_dalek::Keypair { secret: secret_key, public: public_key })
    }
}
