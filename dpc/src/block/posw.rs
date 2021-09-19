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
use snarkvm_utilities::{FromBytes, ToBytes};

use serde::{
    de::{Error as DeserializeError, SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize,
    Deserializer,
    Serialize,
    Serializer,
};
use std::{
    fmt::{
        Debug,
        Display,
        Formatter,
        {self},
    },
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    ops::Deref,
};

/// A Proof of Succinct Work is a SNARK proof.
#[derive(Clone, PartialEq, Eq)]
pub struct ProofOfSuccinctWork<N: Network>(N::PoSWProof);

impl<N: Network> ProofOfSuccinctWork<N> {
    // pub fn new(proof: &[u8]) -> Self {
    //     assert_eq!(proof.len(), Self::size());
    //     Self(proof.to_vec(), PhantomData)
    // }

    pub fn new(proof: N::PoSWProof) -> Self {
        Self(proof)
    }

    /// Returns the proof size in bytes.
    pub fn size() -> usize {
        N::POSW_PROOF_SIZE_IN_BYTES
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

impl<'de, N: Network> Deserialize<'de> for ProofOfSuccinctWork<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct ArrayVisitor<N: Network>(PhantomData<N>);

        impl<'de, N: Network> Visitor<'de> for ArrayVisitor<N> {
            type Value = ProofOfSuccinctWork<N>;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("a valid proof")
            }

            fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<ProofOfSuccinctWork<N>, S::Error> {
                let mut bytes = vec![0; ProofOfSuccinctWork::<N>::size()];
                for b in &mut bytes[..] {
                    *b = seq
                        .next_element()?
                        .ok_or_else(|| DeserializeError::custom("could not read bytes"))?;
                }
                Ok(ProofOfSuccinctWork::read_le(&bytes[..]).expect("Failed to deserialize proof"))
            }
        }

        deserializer.deserialize_tuple(Self::size(), ArrayVisitor::<N>(PhantomData))
    }
}

impl<N: Network> Serialize for ProofOfSuccinctWork<N> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut tup = s.serialize_tuple(Self::size())?;
        for byte in &self.to_bytes_le().expect("Failed to serialize proof") {
            tup.serialize_element(byte)?;
        }
        tup.end()
    }
}

impl<N: Network> Display for ProofOfSuccinctWork<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            hex::encode(&self.to_bytes_le().expect("Failed to serialize proof for Display"))
        )
    }
}

impl<N: Network> Debug for ProofOfSuccinctWork<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "ProofOfSuccinctWork({})",
            hex::encode(&self.to_bytes_le().expect("Failed to serialize proof for Debug"))
        )
    }
}

impl<N: Network> Deref for ProofOfSuccinctWork<N> {
    type Target = N::PoSWProof;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
