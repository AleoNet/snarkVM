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

use crate::prelude::*;
use snarkvm_algorithms::merkle_tree::MerklePath;

#[allow(unused)]
/// A ledger proof of inclusion.
pub struct LedgerProof<N: Network> {
    pub(super) block_hash: N::BlockHash,
    pub(super) previous_block_hash: N::BlockHash,
    pub(super) header_root: N::BlockHeaderRoot,
    pub(super) header_inclusion_proof: MerklePath<N::BlockHeaderTreeParameters>,
    pub(super) commitments_root: N::CommitmentsRoot,
    pub(super) commitment_inclusion_proofs: Vec<MerklePath<N::CommitmentsTreeParameters>>,
}

impl<N: Network> LedgerProof<N> {
    // pub fn new<L: CommitmentsTreeScheme<N>>(ledger: &L, input_records: Vec<Record<N>>) -> Result<Self> {
    //     let commitments_root = ledger.root();
    //
    //     // Compute the ledger membership witnesses.
    //     let mut commitment_inclusion_proofs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
    //     for record in input_records.iter().take(N::NUM_INPUT_RECORDS) {
    //         commitment_inclusion_proofs.push(match record.is_dummy() {
    //             true => MerklePath::default(),
    //             false => ledger.to_commitment_inclusion_proof(&record.commitment())?,
    //         });
    //     }
    //
    //     Ok(Self {
    //         commitments_root,
    //         commitment_inclusion_proofs,
    //     })
    // }

    pub fn commitments_root(&self) -> N::CommitmentsRoot {
        self.commitments_root
    }

    pub fn commitment_inclusion_proofs(&self) -> Vec<MerklePath<N::CommitmentsTreeParameters>> {
        self.commitment_inclusion_proofs.clone()
    }
}

impl<N: Network> Default for LedgerProof<N> {
    fn default() -> Self {
        Self {
            block_hash: Default::default(),
            previous_block_hash: Default::default(),
            header_root: Default::default(),
            header_inclusion_proof: MerklePath::default(),
            commitments_root: Default::default(),
            commitment_inclusion_proofs: vec![MerklePath::default(); N::NUM_INPUT_RECORDS].into(),
        }
    }
}
