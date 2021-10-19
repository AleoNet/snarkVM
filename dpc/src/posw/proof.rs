// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::Network;
use snarkvm_utilities::{fmt, str::FromStr, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    io::{Read, Result as IoResult, Write},
    ops::Deref,
};

/// A Proof of Succinct Work is a SNARK proof.
#[derive(Clone, PartialEq, Eq)]
pub struct ProofOfSuccinctWork<N: Network>(N::PoSWProof);

impl<N: Network> ProofOfSuccinctWork<N> {
    pub fn new(proof: N::PoSWProof) -> Self {
        Self(proof)
    }
}

impl<N: Network> From<&N::PoSWProof> for ProofOfSuccinctWork<N> {
    #[inline]
    fn from(proof: &N::PoSWProof) -> Self {
        Self::new(proof.clone())
    }
}

impl<N: Network> FromBytes for ProofOfSuccinctWork<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self::new(FromBytes::read_le(&mut reader)?))
    }
}

impl<N: Network> ToBytes for ProofOfSuccinctWork<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for ProofOfSuccinctWork<N> {
    type Err = anyhow::Error;

    fn from_str(proof_hex: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_bytes_le(&hex::decode(proof_hex)?)?)
    }
}

impl<N: Network> fmt::Display for ProofOfSuccinctWork<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let bytes = self.to_bytes_le().expect("Failed to convert PoSW proof to bytes");
        write!(f, "{}", hex::encode(bytes))
    }
}

impl<N: Network> Serialize for ProofOfSuccinctWork<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ProofOfSuccinctWork<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "PoSW proof", N::POSW_PROOF_SIZE_IN_BYTES)
            }
        }
    }
}

impl<N: Network> fmt::Debug for ProofOfSuccinctWork<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let bytes = self.to_bytes_le().expect("Failed to convert PoSW proof to bytes");
        write!(f, "ProofOfSuccinctWork({})", hex::encode(bytes))
    }
}

impl<N: Network> Deref for ProofOfSuccinctWork<N> {
    type Target = N::PoSWProof;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
