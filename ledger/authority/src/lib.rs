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

use console::{
    account::{Address, PrivateKey, Signature},
    network::Network,
    prelude::{
        de,
        error,
        fmt,
        ser,
        Debug,
        Deserialize,
        DeserializeExt,
        Deserializer,
        Display,
        Error,
        Formatter,
        FromBytes,
        FromBytesDeserializer,
        FromStr,
        IoResult,
        Read,
        Serialize,
        SerializeStruct,
        Serializer,
        ToBytes,
        ToBytesSerializer,
        Write,
    },
    types::Field,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};

/// A helper type to represent the compact batch certificates.
pub type CompactCertificates = u64;

#[derive(PartialEq, Eq)]
pub enum Authority<N: Network> {
    Beacon(Signature<N>),
    Quorum(CompactCertificates),
}

impl<N: Network> Authority<N> {
    /// Initializes a new beacon authority.
    pub fn new_beacon<R: Rng + CryptoRng>(
        private_key: &PrivateKey<N>,
        block_hash: Field<N>,
        rng: &mut R,
    ) -> Result<Self> {
        // Sign the block hash.
        let signature = private_key.sign(&[block_hash], rng)?;
        // Return the beacon authority.
        Ok(Self::Beacon(signature))
    }

    /// Initializes a new quorum authority.
    pub fn new_quorum(certificates: CompactCertificates) -> Self {
        Self::Quorum(certificates)
    }
}

impl<N: Network> Authority<N> {
    /// Initializes a new beacon authority from the given signature.
    pub fn from_beacon(signature: Signature<N>) -> Self {
        Self::Beacon(signature)
    }

    /// Initializes a new quorum authority.
    pub fn from_quorum(certificates: CompactCertificates) -> Self {
        Self::Quorum(certificates)
    }
}

impl<N: Network> Authority<N> {
    /// Returns `true` if the authority is a beacon.
    pub fn is_beacon(&self) -> bool {
        matches!(self, Self::Beacon(_))
    }

    /// Returns `true` if the authority is a quorum.
    pub fn is_quorum(&self) -> bool {
        matches!(self, Self::Quorum(_))
    }
}

impl<N: Network> Authority<N> {
    /// Returns address of the authority.
    /// If the authority is a beacon, the address of the signer is returned.
    /// If the authority is a quorum, the address of the leader is returned.
    #[allow(deprecated)]
    pub fn to_address(&self) -> Address<N> {
        match self {
            Self::Beacon(signature) => signature.to_address(),
            Self::Quorum(..) => Address::zero(),
        }
    }
}

#[cfg(test)]
mod test_helpers {
    use super::*;
    use console::prelude::{TestRng, Uniform};

    pub type CurrentNetwork = console::network::Testnet3;

    pub fn sample_authorities(rng: &mut TestRng) -> Vec<Authority<CurrentNetwork>> {
        vec![
            Authority::new_beacon(&PrivateKey::new(rng).unwrap(), Field::rand(rng), rng).unwrap(),
            Authority::new_quorum(rng.gen()),
        ]
    }
}
