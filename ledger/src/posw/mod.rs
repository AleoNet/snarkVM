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

use snarkvm_dpc::{merkle_root_with_subroots, MaskedMerkleRoot, MerkleRoot, Network};

use anyhow::Result;

/// PoSW instantiated over BLS12-377 with Marlin.
/// A 32 byte mask is sufficient for Pedersen hashes on BLS12-377, leaves and the root.
pub type PoswMarlin<N> = Posw<N, 32>;

/// Subtree calculation
pub fn txids_to_roots<N: Network>(
    transaction_ids: &[[u8; 32]],
) -> Result<(MerkleRoot, MaskedMerkleRoot, Vec<[u8; 32]>)> {
    use snarkvm_utilities::ToBytes;

    assert!(
        !transaction_ids.is_empty(),
        "Cannot compute a Merkle tree with no transaction IDs"
    );

    let (root, subroots) = merkle_root_with_subroots(N::merkle_tree_crh(), transaction_ids, N::MASKED_TREE_DEPTH);
    let mut merkle_root_bytes = [0u8; 32];
    merkle_root_bytes[..].copy_from_slice(&root);

    let masked_merkle_root_bytes = snarkvm_algorithms::merkle_tree::MerkleTree::<N::MaskedMerkleTreeParameters>::new(
        std::sync::Arc::new(N::masked_merkle_tree_parameters().clone()),
        &subroots,
    )?
    .root()
    .to_bytes_le()?;

    Ok((
        MerkleRoot(merkle_root_bytes.clone()),
        MaskedMerkleRoot::new(&masked_merkle_root_bytes),
        subroots,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_dpc::testnet2::Testnet2;
    use snarkvm_utilities::FromBytes;

    use rand::{rngs::ThreadRng, thread_rng, Rng};

    #[test]
    fn test_load_verify_only() {
        let _params = PoswMarlin::<Testnet2>::verify_only().unwrap();
    }

    #[test]
    fn test_load() {
        let _params = PoswMarlin::<Testnet2>::load().unwrap();
    }

    #[test]
    fn test_posw_marlin() {
        let mut rng = thread_rng();

        // run the trusted setup
        let max_degree = snarkvm_marlin::AHPForR1CS::<Fr>::max_degree(10000, 10000, 100000).unwrap();
        let universal_srs = <Testnet2 as Network>::PoswSNARK::universal_setup(&max_degree, &mut rng).unwrap();

        // run the deterministic setup
        let posw =
            PoswMarlin::<Testnet2>::index::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(&universal_srs)).unwrap();

        // super low difficulty so we find a solution immediately
        let difficulty_target = 0xFFFF_FFFF_FFFF_FFFF_u64;

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

        let (_, pedersen_merkle_root, subroots) = txids_to_roots::<Testnet2>(&transaction_ids).unwrap();

        // generate the proof
        let (nonce, proof) = posw
            .mine(&subroots, difficulty_target, &mut rng, std::u32::MAX)
            .unwrap();

        assert_eq!(proof.len(), 771); // NOTE: Marlin proofs use compressed serialization

        let proof = <<Testnet2 as Network>::PoswSNARK as SNARK>::Proof::read_le(&proof[..]).unwrap();
        posw.verify(nonce, &proof, &pedersen_merkle_root).unwrap();
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
                let (root, pedersen_root, _subroots) = txids_to_roots::<Testnet2>(&tx_ids).unwrap();
                (root, pedersen_root)
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
