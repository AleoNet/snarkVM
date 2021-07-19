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

use crate::traits::{BlockScheme, DPCComponents, TransactionScheme};
use snarkvm_algorithms::merkle_tree::{MerklePath, MerkleTreeDigest};

use std::{path::Path, sync::Arc};

// pub(crate) type RecordCommitment<C: DPCComponents> = ;
// pub(crate) type RecordCommitmentMerklePath<C: DPCComponents> = ;
// pub(crate) type RecordCommitmentMerkleTreeParameters<C: DPCComponents> = ;
// pub(crate) type RecordCommitmentMerkleTreeDigest<C: DPCComponents> = ;
// pub(crate) type RecordSerialNumber<C: DPCComponents> = ;

pub trait LedgerScheme<C: DPCComponents>: Sized {
    type Block: BlockScheme;
    // type Commitment = <C::RecordCommitment as CommitmentScheme>::Output;
    // type MerkleParameters = ;
    // type MerklePath = ;
    // type MerkleTreeDigest = MerkleTreeDigest<C::LedgerMerkleTreeParameters>;
    // type SerialNumber = <C::AccountSignature as SignatureScheme>::PublicKey;
    type Transaction: TransactionScheme;

    /// Instantiates a new ledger with a genesis block.
    fn new(
        path: Option<&Path>,
        parameters: Arc<C::LedgerMerkleTreeParameters>,
        genesis_block: Self::Block,
    ) -> anyhow::Result<Self>;

    /// Return the parameters used to construct the ledger Merkle tree.
    fn parameters(&self) -> &Arc<C::LedgerMerkleTreeParameters>;

    /// Returns the number of blocks including the genesis block
    fn block_height(&self) -> usize;

    /// Return a digest of the latest ledger Merkle tree.
    fn latest_digest(&self) -> Option<MerkleTreeDigest<C::LedgerMerkleTreeParameters>>;

    /// Check that st_{ts} is a valid digest for some (past) ledger state.
    fn validate_digest(&self, digest: &MerkleTreeDigest<C::LedgerMerkleTreeParameters>) -> bool;

    /// Returns true if the given commitment exists in the ledger.
    fn contains_commitment(&self, commitment: &C::RecordCommitmentOutput) -> bool;

    /// Returns true if the given serial number exists in the ledger.
    fn contains_serial_number(&self, serial_number: &C::AccountSignaturePublicKey) -> bool;

    /// Returns the Merkle path to the latest ledger digest
    /// for a given commitment, if it exists in the ledger.
    fn prove_cm(&self, cm: &C::RecordCommitmentOutput) -> anyhow::Result<MerklePath<C::LedgerMerkleTreeParameters>>;
}
