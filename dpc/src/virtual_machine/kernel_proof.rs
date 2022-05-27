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

use snarkvm_algorithms::{SNARKError, SNARK};
use snarkvm_utilities::{FromBytes, FromBytesDeserializer, ToBytes, ToBytesSerializer};

use anyhow::Result;
use serde::{de, ser::SerializeStruct, Deserialize, Deserializer, Serialize, Serializer};

use crate::{InputPublicVariables, Network, OutputPublicVariables};

/// Program ID, program path, verifying key, and proof.
#[derive(Clone, Derivative)]
#[derivative(Debug(bound = "N: Network"), PartialEq(bound = "N: Network"), Eq(bound = "N: Network"))]
pub struct KernelProof<N: Network> {
    pub input_proof: Option<N::InputProof>,
    pub output_proof: Option<N::OutputProof>,
}

impl<N: Network> KernelProof<N> {
    pub fn verify(
        &self,
        input_public_variables: &[InputPublicVariables<N>],
        output_public_variables: &[OutputPublicVariables<N>],
    ) -> Result<bool, SNARKError> {
        let input_is_valid = match input_public_variables.is_empty() {
            true => true,
            false => N::InputSNARK::verify_batch(
                N::input_verifying_key(),
                input_public_variables,
                self.input_proof.as_ref().unwrap(),
            )?,
        };
        let output_is_valid = match output_public_variables.is_empty() {
            true => true,
            false => N::OutputSNARK::verify_batch(
                N::output_verifying_key(),
                output_public_variables,
                self.output_proof.as_ref().unwrap(),
            )?,
        };
        Ok(input_is_valid & output_is_valid)
    }
}

impl<N: Network> ToBytes for KernelProof<N> {
    fn write_le<W: snarkvm_utilities::Write>(&self, mut writer: W) -> std::io::Result<()>
    where
        Self: Sized,
    {
        self.input_proof.is_some().write_le(&mut writer)?;
        if let Some(proof) = &self.input_proof {
            proof.write_le(&mut writer)?;
        }
        self.output_proof.is_some().write_le(&mut writer)?;
        if let Some(proof) = &self.output_proof {
            proof.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<N: Network> FromBytes for KernelProof<N> {
    fn read_le<R: snarkvm_utilities::Read>(mut reader: R) -> std::io::Result<Self>
    where
        Self: Sized,
    {
        let input_proof_is_present: bool = FromBytes::read_le(&mut reader)?;
        let input_proof = input_proof_is_present.then(|| N::InputProof::read_le(&mut reader)).transpose()?;
        let output_proof_is_present: bool = FromBytes::read_le(&mut reader)?;
        let output_proof = output_proof_is_present.then(|| N::OutputProof::read_le(&mut reader)).transpose()?;
        Ok(KernelProof { input_proof, output_proof })
    }
}

impl<N: Network> Serialize for KernelProof<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut proof = serializer.serialize_struct("kernel_proof", 2)?;
                proof.serialize_field("input_proof", &self.input_proof)?;
                proof.serialize_field("output_proof", &self.output_proof)?;
                proof.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de, N: Network> Deserialize<'de> for KernelProof<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                let kernel_proof = serde_json::Value::deserialize(deserializer)?;
                // Recover the execution.
                Ok(Self {
                    input_proof: serde_json::from_value(kernel_proof["input_proof"].clone())
                        .map_err(de::Error::custom)?,
                    output_proof: serde_json::from_value(kernel_proof["output_proof"].clone())
                        .map_err(de::Error::custom)?,
                })
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "kernel_proof"),
        }
    }
}
