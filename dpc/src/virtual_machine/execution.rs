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

use crate::{Network, ProgramPublicVariables};
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};
use snarkvm_utilities::{error, FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    str::FromStr,
};

/// Program ID, program path, verifying key, and proof.
#[derive(Clone, Derivative)]
#[derivative(Debug(bound = "N: Network"), PartialEq(bound = "N: Network"), Eq(bound = "N: Network"))]
pub struct ProgramExecution<N: Network> {
    pub program_id: N::ProgramID,
    pub program_path: MerklePath<N::ProgramIDParameters>,
    #[derivative(Debug = "ignore")]
    pub verifying_key: N::ProgramVerifyingKey,
    pub program_proof: N::ProgramProof,
}

impl<N: Network> ProgramExecution<N> {
    pub fn from(
        program_id: N::ProgramID,
        program_path: MerklePath<N::ProgramIDParameters>,
        verifying_key: N::ProgramVerifyingKey,
        program_proof: N::ProgramProof,
    ) -> Result<Self> {
        Ok(Self { program_id, program_path, verifying_key, program_proof })
    }
}

/// Program execution and inner proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Execution<N: Network> {
    pub program_execution: Option<ProgramExecution<N>>,
}

impl<N: Network> Execution<N> {
    pub fn from(program_execution: Option<ProgramExecution<N>>) -> Result<Self> {
        Ok(Self { program_execution })
    }

    /// Returns `true` if the program execution is valid.
    #[inline]
    pub fn verify(&self, transition_id: N::TransitionID) -> bool {
        if let Some(program_execution) = &self.program_execution {
            // Returns `false` if the program proof is invalid.
            match N::ProgramSNARK::verify(
                &program_execution.verifying_key,
                &ProgramPublicVariables::new(transition_id),
                &program_execution.program_proof,
            ) {
                Ok(true) => true,
                Ok(false) => {
                    eprintln!("Program proof failed to verify");
                    false
                }
                Err(error) => {
                    eprintln!("Failed to validate the program proof: {:?}", error);
                    false
                }
            }
        } else {
            // TODO (howardwu): CRITICAL - Check the program ID is a noop. (Also rearchitect program ID out of ProgramExecution)
            true
        }
    }
}

impl<N: Network> FromBytes for Execution<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_execution_exists: bool = FromBytes::read_le(&mut reader)?;
        let program_execution: Option<ProgramExecution<N>> = match program_execution_exists {
            true => Some(FromBytes::read_le(&mut reader)?),
            false => None,
        };

        Self::from(program_execution).map_err(|e| error(format!("Failed to deserialize execution: {e}")))
    }
}

impl<N: Network> ToBytes for Execution<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        match &self.program_execution {
            Some(program_execution) => {
                true.write_le(&mut writer)?;
                program_execution.program_id.write_le(&mut writer)?;
                program_execution.program_path.write_le(&mut writer)?;
                program_execution.verifying_key.write_le(&mut writer)?;
                program_execution.program_proof.write_le(&mut writer)
            }
            None => false.write_le(&mut writer),
        }
    }
}

impl<N: Network> FromStr for Execution<N> {
    type Err = anyhow::Error;

    #[inline]
    fn from_str(execution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(execution)?)
    }
}

impl<N: Network> fmt::Display for Execution<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for Execution<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut execution = serializer.serialize_struct("Execution", 1)?;
                execution.serialize_field("program_execution", &self.program_execution)?;
                execution.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for Execution<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let execution = serde_json::Value::deserialize(deserializer)?;
                // Recover the execution.
                Self::from(serde_json::from_value(execution["program_execution"].clone()).map_err(de::Error::custom)?)
                    .map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "execution"),
        }
    }
}

impl<N: Network> FromBytes for ProgramExecution<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id = FromBytes::read_le(&mut reader)?;
        let program_path = FromBytes::read_le(&mut reader)?;
        let verifying_key = FromBytes::read_le(&mut reader)?;
        let program_proof = FromBytes::read_le(&mut reader)?;

        Ok(Self { program_id, program_path, verifying_key, program_proof })
    }
}

// TODO (raychu86): Create a new rust file for programExecution or move inner_proof up to the transition level.

impl<N: Network> ToBytes for ProgramExecution<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.program_path.write_le(&mut writer)?;
        self.verifying_key.write_le(&mut writer)?;
        self.program_proof.write_le(&mut writer)
    }
}

impl<N: Network> FromStr for ProgramExecution<N> {
    type Err = anyhow::Error;

    #[inline]
    fn from_str(program_execution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(program_execution)?)
    }
}

impl<N: Network> fmt::Display for ProgramExecution<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(serde::ser::Error::custom)?)
    }
}

impl<N: Network> Serialize for ProgramExecution<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut execution = serializer.serialize_struct("ProgramExecution", 4)?;
                execution.serialize_field("program_id", &self.program_id)?;
                execution.serialize_field("program_path", &self.program_path)?;
                execution.serialize_field("verifying_key", &self.verifying_key)?;
                execution.serialize_field("program_proof", &self.program_proof)?;
                execution.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for ProgramExecution<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let program_execution = serde_json::Value::deserialize(deserializer)?;
                // Recover the program execution.
                Self::from(
                    serde_json::from_value(program_execution["program_id"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(program_execution["program_path"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(program_execution["verifying_key"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(program_execution["program_proof"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "program_execution"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testnet2::Testnet2;

    #[test]
    fn test_execution_serde_json() {
        let coinbase_transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let execution = coinbase_transaction.transitions()[0].execution().clone();

        // Serialize
        let expected_string = execution.to_string();
        let candidate_string = serde_json::to_string(&execution).unwrap();
        assert_eq!(expected_string, candidate_string);

        // Deserialize
        assert_eq!(execution, Execution::<Testnet2>::from_str(&candidate_string).unwrap());
        assert_eq!(execution, serde_json::from_str(&candidate_string).unwrap());
    }

    #[test]
    fn test_execution_bincode() {
        let coinbase_transaction = Testnet2::genesis_block().to_coinbase_transaction().unwrap();
        let execution = coinbase_transaction.transitions()[0].execution().clone();

        // Serialize
        let expected_bytes = execution.to_bytes_le().unwrap();
        let candidate_bytes = bincode::serialize(&execution).unwrap();
        // TODO (howardwu): Serialization - Handle the inconsistency between ToBytes and Serialize (off by a length encoding).
        assert_eq!(&expected_bytes[..], &candidate_bytes[8..]);

        // Deserialize
        assert_eq!(execution, Execution::<Testnet2>::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(execution, bincode::deserialize(&candidate_bytes[..]).unwrap());
    }
}
