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

use crate::{AleoAmount, InnerPublicVariables, Network, ProgramPublicVariables};
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};
use std::io::{Error, ErrorKind, Read, Result as IoResult, Write};

/// Program ID, program path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Execution<N: Network> {
    pub program_id: N::ProgramID,
    pub program_path: MerklePath<N::ProgramIDParameters>,
    #[derivative(Debug = "ignore")]
    pub verifying_key: N::ProgramVerifyingKey,
    pub program_proof: N::ProgramProof,
    pub inner_proof: N::InnerProof,
}

impl<N: Network> Execution<N> {
    pub fn from(
        program_id: N::ProgramID,
        program_path: MerklePath<N::ProgramIDParameters>,
        verifying_key: N::ProgramVerifyingKey,
        program_proof: N::ProgramProof,
        inner_proof: N::InnerProof,
    ) -> Result<Self> {
        Ok(Self {
            program_id,
            program_path,
            verifying_key,
            program_proof,
            inner_proof,
        })
    }

    /// Returns `true` if the program execution is valid.
    #[inline]
    pub fn verify(
        &self,
        inner_verifying_key: &<N::InnerSNARK as SNARK>::VerifyingKey,
        transition_id: N::TransitionID,
        value_balance: AleoAmount,
        ledger_root: N::LedgerRoot,
        local_transitions_root: N::TransactionID,
    ) -> bool {
        // Returns `false` if the inner proof is invalid.
        match N::InnerSNARK::verify(
            inner_verifying_key,
            &InnerPublicVariables::new(
                transition_id,
                value_balance,
                ledger_root,
                local_transitions_root,
                Some(self.program_id),
            ),
            &self.inner_proof,
        ) {
            Ok(is_valid) => {
                if !is_valid {
                    eprintln!("Inner proof failed to verify");
                    return false;
                }
            }
            Err(error) => {
                eprintln!("Failed to validate the inner proof: {:?}", error);
                return false;
            }
        };

        // Returns `false` if the program proof is invalid.
        match N::ProgramSNARK::verify(
            &self.verifying_key,
            &ProgramPublicVariables::new(transition_id),
            &self.program_proof,
        ) {
            Ok(is_valid) => match is_valid {
                true => true,
                false => {
                    eprintln!("Program proof failed to verify");
                    false
                }
            },
            Err(error) => {
                eprintln!("Failed to validate the program proof: {:?}", error);
                false
            }
        }
    }
}

impl<N: Network> FromBytes for Execution<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let program_id = FromBytes::read_le(&mut reader)?;
        let program_path = FromBytes::read_le(&mut reader)?;
        let verifying_key = FromBytes::read_le(&mut reader)?;
        let program_proof = FromBytes::read_le(&mut reader)?;
        let inner_proof = FromBytes::read_le(&mut reader)?;

        Self::from(program_id, program_path, verifying_key, program_proof, inner_proof)
            .map_err(|error| Error::new(ErrorKind::Other, format!("{}", error)))
    }
}

impl<N: Network> ToBytes for Execution<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.program_id.write_le(&mut writer)?;
        self.program_path.write_le(&mut writer)?;
        self.verifying_key.write_le(&mut writer)?;
        self.program_proof.write_le(&mut writer)?;
        self.inner_proof.write_le(&mut writer)
    }
}

impl<N: Network> Serialize for Execution<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut execution = serializer.serialize_struct("Execution", 5)?;
                execution.serialize_field("program_id", &self.program_id)?;
                execution.serialize_field("program_path", &self.program_path)?;
                execution.serialize_field("verifying_key", &self.verifying_key)?;
                execution.serialize_field("program_proof", &self.program_proof)?;
                execution.serialize_field("inner_proof", &self.inner_proof)?;
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
                Self::from(
                    serde_json::from_value(execution["program_id"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(execution["program_path"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(execution["verifying_key"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(execution["program_proof"].clone()).map_err(de::Error::custom)?,
                    serde_json::from_value(execution["inner_proof"].clone()).map_err(de::Error::custom)?,
                )
                .map_err(de::Error::custom)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "execution"),
        }
    }
}
