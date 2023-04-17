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

use crate::{
    polycommit::sonic_pc,
    snark::marlin::{ahp::indexer::*, CircuitVerifyingKey, MarlinMode},
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
pub struct CircuitProvingKey<E: PairingEngine, MM: MarlinMode> {
    /// The circuit verifying key.
    pub circuit_verifying_key: CircuitVerifyingKey<E, MM>,
    /// The randomness for the circuit polynomial commitments.
    pub circuit_commitment_randomness: Vec<sonic_pc::Randomness<E>>,
    // NOTE: The circuit verifying key's circuit_info and circuit id are also stored in Circuit for convenience.
    /// The circuit itself.
    pub circuit: Arc<Circuit<E::Fr, MM>>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: Arc<sonic_pc::CommitterKey<E>>,
}

impl<E: PairingEngine, MM: MarlinMode> ToBytes for CircuitProvingKey<E, MM> {
    fn write_le<W: Write>(&self, mut writer: W) -> io::Result<()> {
        CanonicalSerialize::serialize_compressed(&self.circuit_verifying_key, &mut writer)?;
        CanonicalSerialize::serialize_compressed(&self.circuit_commitment_randomness, &mut writer)?;
        CanonicalSerialize::serialize_compressed(&self.circuit, &mut writer)?;

        self.committer_key.write_le(&mut writer)
    }
}

impl<E: PairingEngine, MM: MarlinMode> FromBytes for CircuitProvingKey<E, MM> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> io::Result<Self> {
        let circuit_verifying_key = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let circuit_commitment_randomness = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let circuit = CanonicalDeserialize::deserialize_compressed(&mut reader)?;
        let committer_key = Arc::new(FromBytes::read_le(&mut reader)?);

        Ok(Self { circuit_verifying_key, circuit_commitment_randomness, circuit, committer_key })
    }
}

impl<E: PairingEngine, MM: MarlinMode> Ord for CircuitProvingKey<E, MM> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.circuit.id.cmp(&other.circuit.id)
    }
}

impl<E: PairingEngine, MM: MarlinMode> PartialOrd for CircuitProvingKey<E, MM> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
