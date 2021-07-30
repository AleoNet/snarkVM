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

use crate::Parameters;
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTreeDigest};

/// The record commitment tree is a core state tree of the ledger.
pub trait RecordCommitmentTree<C: Parameters>: Sized {
    /// Return the latest state root of the record commitment tree.
    fn latest_digest(&self) -> Option<MerkleTreeDigest<C::RecordCommitmentTreeParameters>>;

    /// Check that st_{ts} is a valid state root for some (past) record commitment tree.
    fn is_valid_digest(&self, digest: &MerkleTreeDigest<C::RecordCommitmentTreeParameters>) -> bool;

    /// Returns true if the given commitment exists in the record commitment tree.
    fn contains_commitment(&self, commitment: &C::RecordCommitment) -> bool;

    /// Returns the Merkle path to the latest state root for a given record commitment,
    /// if it exists in the record commitment tree.
    fn prove_cm(&self, cm: &C::RecordCommitment) -> anyhow::Result<MerklePath<C::RecordCommitmentTreeParameters>>;
}

/// The record serial number tree is a core state tree of the ledger.
pub trait RecordSerialNumberTree<C: Parameters>: Sized {
    /// TODO (howardwu): TEMPORARY - Move this into a RecordSerialNumberTree.
    /// Returns true if the given serial number exists in the record serial number tree.
    fn contains_serial_number(&self, serial_number: &C::AccountSignaturePublicKey) -> bool;
}
