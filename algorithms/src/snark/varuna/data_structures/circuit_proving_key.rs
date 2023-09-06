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

use crate::{
    polycommit::sonic_pc,
    snark::varuna::{ahp::indexer::*, CircuitVerifyingKey, SNARKMode},
};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{
    io::{self, Read, Write},
    serialize::*,
    FromBytes,
    ToBytes,
};

use std::{cmp::Ordering, sync::Arc};

/// Proving key for a specific circuit (i.e., R1CS matrices).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitProvingKey<E: PairingEngine, MM: SNARKMode> {
    /// The circuit verifying key.
    pub circuit_verifying_key: CircuitVerifyingKey<E>,
    /// The randomness for the circuit polynomial commitments.
    pub circuit_commitment_randomness: Vec<sonic_pc::Randomness<E>>,
    // NOTE: The circuit verifying key's circuit_info and circuit id are also stored in Circuit for convenience.
    /// The circuit itself.
    pub circuit: Arc<Circuit<E::Fr, MM>>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: Arc<sonic_pc::CommitterKey<E>>,
}

impl<E: PairingEngine, MM: SNARKMode> ToBytes for CircuitProvingKey<E, MM> {
    fn write_le<W: Write>(&self, mut writer: W) -> io::Result<()> {
        CanonicalSerialize::serialize_compressed(&self.circuit_verifying_key, &mut writer)?;
        CanonicalSerialize::serialize_compressed(&self.circuit_commitment_randomness, &mut writer)?;
        CanonicalSerialize::serialize_compressed(&self.circuit, &mut writer)?;

        self.committer_key.write_le(&mut writer)
    }
}

impl<E: PairingEngine, MM: SNARKMode> FromBytes for CircuitProvingKey<E, MM> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> io::Result<Self> {
        let circuit_verifying_key = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let circuit_commitment_randomness = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let circuit = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let committer_key = Arc::new(FromBytes::read_le(&mut reader)?);

        Ok(Self { circuit_verifying_key, circuit_commitment_randomness, circuit, committer_key })
    }
}

impl<E: PairingEngine, MM: SNARKMode> Ord for CircuitProvingKey<E, MM> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.circuit.id.cmp(&other.circuit.id)
    }
}

impl<E: PairingEngine, MM: SNARKMode> PartialOrd for CircuitProvingKey<E, MM> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
