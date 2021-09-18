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

pub mod circuit;

mod posw;
use posw::Posw;

use snarkvm_dpc::{merkle_root_with_subroots, MerkleRoot, Network};

use anyhow::Result;

/// PoSW instantiated over BLS12-377 with Marlin.
/// A 32 byte mask is sufficient for Pedersen hashes on BLS12-377, leaves and the root.
pub type PoswMarlin<N> = Posw<N, 32>;

/// Subtree calculation
pub fn txids_to_roots<N: Network>(transaction_ids: &[[u8; 32]]) -> Result<(MerkleRoot, N::PoswRoot, Vec<[u8; 32]>)> {
    assert!(
        !transaction_ids.is_empty(),
        "Cannot compute a Merkle tree with no transaction IDs"
    );

    // START DELETE
    type MerkleTreeCRH =
        snarkvm_algorithms::crh::BHPCompressedCRH<snarkvm_curves::edwards_bls12::EdwardsProjective, 16, 32>;

    use once_cell::sync::OnceCell;
    use snarkvm_algorithms::CRH;

    static MERKLE_TREE_CRH: OnceCell<MerkleTreeCRH> = OnceCell::new();
    let crh = MERKLE_TREE_CRH.get_or_init(|| MerkleTreeCRH::setup("MerkleTreeCRH"));
    // END DELETE

    let (root, subroots) = merkle_root_with_subroots(crh, transaction_ids, N::POSW_TREE_DEPTH);
    let mut merkle_root_bytes = [0u8; 32];
    merkle_root_bytes[..].copy_from_slice(&root);

    let masked_root = snarkvm_algorithms::merkle_tree::MerkleTree::<N::PoswTreeParameters>::new(
        std::sync::Arc::new(N::posw_tree_parameters().clone()),
        &subroots,
    )?
    .root()
    .clone();

    Ok((MerkleRoot(merkle_root_bytes.clone()), masked_root, subroots))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::posw::circuit::POSWCircuit;
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_dpc::testnet2::Testnet2;
    use snarkvm_marlin::ahp::AHPForR1CS;
    use snarkvm_utilities::ToBytes;

    use rand::{rngs::ThreadRng, thread_rng, Rng};

    #[test]
    fn test_load() {
        let _params = PoswMarlin::<Testnet2>::load(true).unwrap();
    }

    #[test]
    fn test_posw_marlin() {
        let rng = &mut thread_rng();

        // Construct an instance of PoSW.
        let posw = {
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(10000, 10000, 100000).unwrap();
            let universal_srs = <<Testnet2 as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, rng).unwrap();
            PoswMarlin::<Testnet2>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(&universal_srs)).unwrap()
        };

        // Construct an assigned circuit.
        let nonce = 1u32;
        let block_header_leaves = vec![[3u8; 32]; 4];
        let assigned_circuit = POSWCircuit::<Testnet2, 32>::new(nonce, &block_header_leaves).unwrap();
        let difficulty_target = u64::MAX;

        let (nonce, proof) = posw
            .mine(&block_header_leaves, difficulty_target, rng, u32::MAX)
            .unwrap();
        assert_eq!(proof.to_bytes_le().unwrap().len(), 771); // NOTE: Marlin proofs use compressed serialization

        assert!(posw.verify(nonce, assigned_circuit.root(), difficulty_target, &proof));
    }

    #[test]
    fn test_changing_tx_roots() {
        let mut rng = thread_rng();

        // The number of transactions for which to check subsequent merkle tree root values.
        let num_txs: usize = rng.gen_range(1..256);

        // Create a vector with transaction ids consisting of random values.
        let transaction_ids = {
            let mut vec = Vec::with_capacity(num_txs);
            for _ in 0..num_txs {
                let mut id = [0u8; 32];
                rng.fill(&mut id);
                vec.push(id);
            }
            vec
        };

        // Collect the transactions into a collection of their growing sequences, i.e.
        // [[tx0], [tx0, tx1], [tx0, tx1, tx2], ..., [tx0, ..., num_txs]].
        let growing_tx_ids = transaction_ids
            .into_iter()
            .scan(Vec::with_capacity(num_txs), |acc, tx_id| {
                acc.push(tx_id);
                Some(acc.clone())
            })
            .collect::<Vec<_>>();

        // Calculate the root hashes for the sequences of transactions.
        let subsequent_root_hashes = growing_tx_ids
            .into_iter()
            .map(|tx_ids| {
                let (root, posw_root, _subroots) = txids_to_roots::<Testnet2>(&tx_ids).unwrap();
                (root, posw_root)
            })
            .collect::<Vec<_>>();

        // Ensure that the subsequent roots differ for every new transaction.
        let mut hashes_differ = true;
        for window in subsequent_root_hashes.windows(2) {
            match window {
                [(root1, pedersen_root1), (root2, pedersen_root2)] => {
                    if root1 == root2 || pedersen_root1 == pedersen_root2 {
                        hashes_differ = false;
                        break;
                    }
                }
                _ => unreachable!(),
            }
        }

        assert!(hashes_differ);
    }
}
