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

use crate::prelude::*;
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use std::io::{Read, Result as IoResult, Write};

/// A local proof of inclusion.
#[derive(Clone, Debug)]
pub struct LocalProof<N: Network> {
    transaction_id: N::TransactionID,
    transaction_inclusion_proof: MerklePath<N::TransactionIDParameters>,
    transition_id: N::TransitionID,
    transition_inclusion_proof: MerklePath<N::TransitionIDParameters>,
    commitment: N::Commitment,
}

impl<N: Network> LocalProof<N> {
    ///
    /// Initializes a new instance of `LocalProof`.
    ///
    pub fn new(
        transaction_id: N::TransactionID,
        transaction_inclusion_proof: MerklePath<N::TransactionIDParameters>,
        transition_id: N::TransitionID,
        transition_inclusion_proof: MerklePath<N::TransitionIDParameters>,
        commitment: N::Commitment,
    ) -> Result<Self> {
        // Ensure the transition inclusion proof is valid.
        if !transition_inclusion_proof.verify(&transition_id, &commitment)? {
            return Err(anyhow!("Commitment {} does not belong to transition {}", commitment, transition_id));
        }

        // Ensure the transaction inclusion proof is valid.
        if !transaction_inclusion_proof.verify(&transaction_id, &transition_id)? {
            return Err(anyhow!("Transition {} does not belong to transaction {}", transition_id, transaction_id));
        }

        Ok(Self { transaction_id, transaction_inclusion_proof, transition_id, transition_inclusion_proof, commitment })
    }

    /// Returns the transaction ID.
    pub fn transaction_id(&self) -> N::TransactionID {
        self.transaction_id
    }

    /// Returns the transaction inclusion proof.
    pub fn transaction_inclusion_proof(&self) -> &MerklePath<N::TransactionIDParameters> {
        &self.transaction_inclusion_proof
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the transition inclusion proof.
    pub fn transition_inclusion_proof(&self) -> &MerklePath<N::TransitionIDParameters> {
        &self.transition_inclusion_proof
    }

    /// Returns the commitment.
    pub fn commitment(&self) -> N::Commitment {
        self.commitment
    }
}

impl<N: Network> FromBytes for LocalProof<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let transaction_id = FromBytes::read_le(&mut reader)?;
        let transaction_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let transition_id = FromBytes::read_le(&mut reader)?;
        let transition_inclusion_proof = FromBytes::read_le(&mut reader)?;
        let commitment = FromBytes::read_le(&mut reader)?;

        Ok(Self::new(
            transaction_id,
            transaction_inclusion_proof,
            transition_id,
            transition_inclusion_proof,
            commitment,
        )
        .expect("Failed to deserialize a local inclusion proof"))
    }
}

impl<N: Network> ToBytes for LocalProof<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.transaction_id.write_le(&mut writer)?;
        self.transaction_inclusion_proof.write_le(&mut writer)?;
        self.transition_id.write_le(&mut writer)?;
        self.transition_inclusion_proof.write_le(&mut writer)?;
        self.commitment.write_le(&mut writer)
    }
}

impl<N: Network> Default for LocalProof<N> {
    fn default() -> Self {
        Self {
            transaction_id: Default::default(),
            transaction_inclusion_proof: MerklePath::default(),
            transition_id: Default::default(),
            transition_inclusion_proof: MerklePath::default(),
            commitment: Default::default(),
        }
    }
}
