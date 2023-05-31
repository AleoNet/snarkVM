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
