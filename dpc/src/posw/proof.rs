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

use crate::{Network, PoSWError};
use snarkvm_algorithms::{crypto_hash::sha256d_to_u64, SNARK};
use snarkvm_utilities::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
    FromBytes,
    FromBytesDeserializer,
    ToBytes,
    ToBytesSerializer,
};

use anyhow::{anyhow, Result};
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};

/// A wrapper enum for a PoSW proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoSWProof<N: Network> {
    NonHiding(N::PoSWProof),
}

impl<N: Network> PoSWProof<N> {
    ///
    /// Initializes a new instance of a PoSW proof.
    ///
    pub fn new(proof: N::PoSWProof) -> Self {
        Self::NonHiding(proof)
    }

    ///
    /// Returns `true` if the PoSW proof is hiding.
    ///
    pub fn is_hiding(&self) -> bool {
        match self {
            Self::NonHiding(..) => false,
        }
    }

    ///
    /// Returns the proof difficulty, determined by double-hashing the proof bytes to a u64.
    ///
    pub fn to_proof_difficulty(&self) -> Result<u64> {
        Ok(sha256d_to_u64(&self.to_bytes_le()?))
    }

    ///
    /// Returns `true` if the PoSW proof is valid.
    ///
    pub fn verify(
        &self,
        verifying_key: &<<N as Network>::PoSWSNARK as SNARK>::VerifyingKey,
        inputs: &[N::InnerScalarField],
    ) -> bool {
        match self {
            Self::NonHiding(proof) => {
                // Ensure the proof is valid.
                let check = <<N as Network>::PoSWSNARK as SNARK>::verify(verifying_key, &inputs.to_vec(), proof);
                if check.is_err() || !check.unwrap() {
                    #[cfg(debug_assertions)]
                    eprintln!("PoSW proof verification failed");
                    return false;
                }
            }
        }

        true
    }

    /// Returns the PoSW proof size in bytes.
    pub fn size(&self) -> usize {
        N::HEADER_PROOF_SIZE_IN_BYTES
    }
}

impl<N: Network> FromBytes for PoSWProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut buffer = vec![0u8; N::HEADER_PROOF_SIZE_IN_BYTES];
        reader.read_exact(&mut buffer)?;

        match N::PoSWProof::read_le(&buffer[..]) {
            Ok(proof) => Ok(Self::NonHiding(proof)),
            Err(_) => Err(PoSWError::Message("Failed to deserialize PoSW proof with FromBytes".to_string()).into()),
        }
    }
}

impl<N: Network> ToBytes for PoSWProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        match self {
            Self::NonHiding(proof) => proof.write_le(writer),
        }
    }
}

impl<N: Network> FromStr for PoSWProof<N> {
    type Err = anyhow::Error;

    fn from_str(header: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(header)?)
    }
}

impl<N: Network> fmt::Display for PoSWProof<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for PoSWProof<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut header = serializer.serialize_struct("PoSWProof", 1)?;
                match self {
                    Self::NonHiding(proof) => header.serialize_field("non_hiding", proof)?,
                }
                header.end()
            }
            false => ToBytesSerializer::serialize(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for PoSWProof<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let proof = serde_json::Value::deserialize(deserializer)?;

                if let Ok(proof) = serde_json::from_value(proof["non_hiding"].clone()) {
                    Ok(Self::NonHiding(proof))
                } else {
                    Err(anyhow!("Invalid human-readable deserialization")).map_err(de::Error::custom)?
                }
            }
            false => {
                FromBytesDeserializer::<Self>::deserialize(deserializer, "PoSW proof", N::HEADER_PROOF_SIZE_IN_BYTES)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{prelude::*, testnet1::Testnet1, testnet2::Testnet2, Block};
    use snarkvm_utilities::ToBytes;

    use core::sync::atomic::AtomicBool;
    use rand::thread_rng;

    #[test]
    fn test_posw_no_zk() {
        let rng = &mut thread_rng();
        let recipient = Account::<Testnet2>::new(rng).address();
        let terminator = AtomicBool::new(false);

        let mut ledger = Ledger::<Testnet2>::new().unwrap();

        // Check the genesis block.
        // This will use a non-hiding PoSW Marlin mode.
        {
            assert_eq!(0, ledger.latest_block_height());
            let latest_block_header = ledger.latest_block().unwrap().header().clone();
            let latest_proof = latest_block_header.proof();
            assert_eq!(latest_proof.to_bytes_le().unwrap().len(), Testnet2::HEADER_PROOF_SIZE_IN_BYTES); // NOTE: Marlin proofs use compressed serialization
            assert!(Testnet2::posw().verify_from_block_header(&latest_block_header));
            assert!(!latest_proof.is_hiding());
        }

        // Check block 1.
        // This will use a non-hiding PoSW Marlin mode.
        {
            ledger.mine_next_block(recipient, true, &terminator, rng).unwrap();
            assert_eq!(1, ledger.latest_block_height());

            let latest_block_header = ledger.latest_block().unwrap().header().clone();
            let latest_proof = latest_block_header.proof();
            assert_eq!(latest_proof.to_bytes_le().unwrap().len(), Testnet2::HEADER_PROOF_SIZE_IN_BYTES); // NOTE: Marlin proofs use compressed serialization
            assert!(Testnet2::posw().verify_from_block_header(&latest_block_header));
            assert!(!latest_proof.is_hiding());
        }

        // Check block 2.
        // This will use a non-hiding PoSW Marlin mode.
        {
            ledger.mine_next_block(recipient, true, &terminator, rng).unwrap();
            assert_eq!(2, ledger.latest_block_height());

            let latest_block_header = ledger.latest_block().unwrap().header().clone();
            let latest_proof = latest_block_header.proof();
            assert_eq!(latest_proof.to_bytes_le().unwrap().len(), Testnet2::HEADER_PROOF_SIZE_IN_BYTES); // NOTE: Marlin proofs use compressed serialization
            assert!(Testnet2::posw().verify_from_block_header(&latest_block_header));
            assert!(!latest_proof.is_hiding());
        }
    }

    #[test]
    fn test_genesis_proof() {
        use snarkvm_parameters::Genesis;
        {
            let block =
                Block::<Testnet1>::read_le(&snarkvm_parameters::testnet1::GenesisBlock::load_bytes()[..]).unwrap();
            let proof = block.header().proof();
            assert!(!proof.is_hiding());
            assert_eq!(proof.to_bytes_le().unwrap().len(), Testnet1::HEADER_PROOF_SIZE_IN_BYTES);
            assert_eq!(bincode::serialize(&proof).unwrap().len(), Testnet1::HEADER_PROOF_SIZE_IN_BYTES);
        }
        {
            let block =
                Block::<Testnet2>::read_le(&snarkvm_parameters::testnet2::GenesisBlock::load_bytes()[..]).unwrap();
            let proof = block.header().proof();
            assert!(!proof.is_hiding());
            assert_eq!(proof.to_bytes_le().unwrap().len(), Testnet2::HEADER_PROOF_SIZE_IN_BYTES);
            assert_eq!(bincode::serialize(&proof).unwrap().len(), Testnet2::HEADER_PROOF_SIZE_IN_BYTES);
        }
    }

    #[test]
    fn test_proof_serde_json() {
        {
            let proof = Testnet1::genesis_block().header().proof().clone();

            // Serialize
            let expected_string = proof.to_string();
            let candidate_string = serde_json::to_string(&proof).unwrap();
            assert_eq!(1315, candidate_string.len(), "Update me if serialization has changed");
            assert_eq!(expected_string, candidate_string);

            // Deserialize
            assert_eq!(proof, PoSWProof::from_str(&candidate_string).unwrap());
            assert_eq!(proof, serde_json::from_str(&candidate_string).unwrap());
        }
        {
            let proof = Testnet2::genesis_block().header().proof().clone();

            // Serialize
            let expected_string = proof.to_string();
            let candidate_string = serde_json::to_string(&proof).unwrap();
            assert_eq!(1315, candidate_string.len(), "Update me if serialization has changed");
            assert_eq!(expected_string, candidate_string);

            // Deserialize
            assert_eq!(proof, PoSWProof::from_str(&candidate_string).unwrap());
            assert_eq!(proof, serde_json::from_str(&candidate_string).unwrap());
        }
    }

    #[test]
    fn test_proof_bincode() {
        {
            let proof = Testnet1::genesis_block().header().proof().clone();

            let expected_bytes = proof.to_bytes_le().unwrap();
            assert_eq!(&expected_bytes[..], &bincode::serialize(&proof).unwrap()[..]);

            assert_eq!(proof, PoSWProof::read_le(&expected_bytes[..]).unwrap());
            assert_eq!(proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        }
        {
            let proof = Testnet2::genesis_block().header().proof().clone();

            let expected_bytes = proof.to_bytes_le().unwrap();
            assert_eq!(&expected_bytes[..], &bincode::serialize(&proof).unwrap()[..]);

            assert_eq!(proof, PoSWProof::read_le(&expected_bytes[..]).unwrap());
            assert_eq!(proof, bincode::deserialize(&expected_bytes[..]).unwrap());
        }
    }
}
