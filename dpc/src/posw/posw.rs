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

//! Generic PoSW Miner and Verifier, compatible with any implementer of the SNARK trait.

use crate::{posw::PoSWCircuit, BlockHeader, Network, PoswError};
use snarkvm_algorithms::{crh::sha256d_to_u64, traits::SNARK, SRS};
use snarkvm_fields::ToConstraintField;
use snarkvm_parameters::{
    testnet1::{PoswSNARKPKParameters, PoswSNARKVKParameters},
    traits::Parameter,
};
use snarkvm_profiler::{end_timer, start_timer};
use snarkvm_utilities::{FromBytes, ToBytes};

use rand::{CryptoRng, Rng};

/// A Proof of Succinct Work miner and verifier.
#[derive(Clone)]
pub struct PoSW<N: Network, const MASK_NUM_BYTES: usize> {
    /// The proving key. If not provided, PoSW will work in verify-only mode
    /// and the `mine` function will panic.
    proving_key: Option<<<N as Network>::PoswSNARK as SNARK>::ProvingKey>,
    /// The verifying key.
    verifying_key: <<N as Network>::PoswSNARK as SNARK>::VerifyingKey,
}

impl<N: Network, const MASK_NUM_BYTES: usize> PoSW<N, MASK_NUM_BYTES> {
    /// Sets up an instance of PoSW using an SRS.
    pub fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoswSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoswError> {
        let (proving_key, verifying_key) =
            <<N as Network>::PoswSNARK as SNARK>::setup::<_, R>(&PoSWCircuit::<N, MASK_NUM_BYTES>::blank()?, srs)?;

        Ok(Self {
            proving_key: Some(proving_key),
            verifying_key,
        })
    }

    /// Loads an instance of PoSW using stored parameters.
    pub fn load(is_prover: bool) -> Result<Self, PoswError> {
        let pk = match is_prover {
            true => Some(<<N as Network>::PoswSNARK as SNARK>::ProvingKey::read_le(
                &PoswSNARKPKParameters::load_bytes()?[..],
            )?),
            false => None,
        };
        let vk =
            <<N as Network>::PoswSNARK as SNARK>::VerifyingKey::read_le(&PoswSNARKVKParameters::load_bytes()?[..])?;

        Ok(Self {
            proving_key: pk,
            verifying_key: vk.into(),
        })
    }

    /// Returns a reference to the PoSW circuit proving key.
    pub fn proving_key(&self) -> &Option<<N::PoswSNARK as SNARK>::ProvingKey> {
        &self.proving_key
    }

    /// Returns a reference to the PoSW circuit verifying key.
    pub fn verifying_key(&self) -> &<N::PoswSNARK as SNARK>::VerifyingKey {
        &self.verifying_key
    }

    /// Given the leaves of the block header, it will calculate a PoSW and nonce
    /// such that they are under the difficulty target.
    pub fn mine<R: Rng + CryptoRng>(&self, block_header: &mut BlockHeader<N>, rng: &mut R) -> Result<(), PoswError> {
        let pk = self.proving_key.as_ref().expect("tried to mine without a PK set up");

        loop {
            // Sample a random nonce.
            let nonce = rng.gen_range(0..u32::MAX);
            block_header.set_nonce(nonce);

            // Instantiate the circuit.
            let leaves = block_header.to_leaves()?;
            let circuit = PoSWCircuit::<N, MASK_NUM_BYTES>::new(nonce, &leaves)?;

            // Generate the proof.
            let timer = start_timer!(|| "PoSW proof");
            block_header.set_proof((&<<N as Network>::PoswSNARK as SNARK>::prove(pk, &circuit, rng)?).into());
            end_timer!(timer);

            if self.verify(block_header) {
                break;
            }
        }

        Ok(())
    }

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    pub fn verify(&self, block_header: &BlockHeader<N>) -> bool {
        // Retrieve the proof.
        let proof = match block_header.proof() {
            Some(proof) => proof,
            None => {
                eprintln!("Block header does not have a corresponding PoSW proof");
                return false;
            }
        };

        // Ensure the difficulty target is met.
        match proof.to_bytes_le() {
            Ok(proof) => {
                let hash_difficulty = sha256d_to_u64(&proof);
                if hash_difficulty <= block_header.difficulty_target() {
                    eprintln!("PoSW difficulty target is not met");
                    return false;
                }
            }
            Err(error) => {
                eprintln!("Failed to convert PoSW proof to bytes: {}", error);
                return false;
            }
        };

        let inputs = |(nonce, root): (u32, &N::BlockHeaderRoot)| -> anyhow::Result<Vec<N::InnerScalarField>> {
            // Commit to the nonce and root.
            let mask = PoSWCircuit::<N, MASK_NUM_BYTES>::commit(nonce, root)?;

            // get the mask and the root in public inputs format
            let merkle_root = N::InnerScalarField::read_le(&root.to_bytes_le()?[..])?;
            let inputs = [mask.to_field_elements()?, vec![merkle_root]].concat();
            Ok(inputs)
        };

        // Construct the inputs.
        let inputs = match inputs((block_header.nonce(), &block_header.to_root().unwrap())) {
            Ok(inputs) => inputs,
            Err(error) => {
                eprintln!("{}", error);
                return false;
            }
        };

        // Ensure the proof is valid.
        if !<<N as Network>::PoswSNARK as SNARK>::verify(&self.verifying_key, &inputs, &*proof).unwrap() {
            eprintln!("PoSW proof verification failed");
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use crate::{posw::PoswMarlin, testnet2::Testnet2, BlockHeader, Network, Transaction, Transactions};
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_marlin::ahp::AHPForR1CS;
    use snarkvm_parameters::{testnet2::Transaction1, Genesis};
    use snarkvm_utilities::{FromBytes, ToBytes};

    use rand::{rngs::ThreadRng, thread_rng, Rng};

    #[test]
    fn test_load() {
        let _params = PoswMarlin::<Testnet2>::load(true).unwrap();
    }

    #[test]
    fn test_posw_marlin() {
        // Construct an instance of PoSW.
        let posw = {
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(10000, 10000, 100000).unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            PoswMarlin::<Testnet2>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(&universal_srs)).unwrap()
        };

        // Construct an assigned circuit.
        let mut block_header = BlockHeader::<Testnet2>::new_genesis(
            &Transactions::from(&[Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap()]),
            &mut thread_rng(),
        )
        .unwrap();

        posw.mine(&mut block_header, &mut thread_rng()).unwrap();
        assert!(block_header.proof().is_some());
        assert_eq!(
            block_header.proof().as_ref().unwrap().to_bytes_le().unwrap().len(),
            Testnet2::POSW_PROOF_SIZE_IN_BYTES
        ); // NOTE: Marlin proofs use compressed serialization
        assert!(posw.verify(&block_header));
    }

    #[test]
    fn test_posw_difficulty_target() {
        // Construct an instance of PoSW.
        let posw = {
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(10000, 10000, 100000).unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoswSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            PoswMarlin::<Testnet2>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(&universal_srs)).unwrap()
        };

        // Construct an assigned circuit.
        let mut block_header = BlockHeader::<Testnet2>::new_genesis(
            &Transactions::from(&[Transaction::<Testnet2>::from_bytes_le(&Transaction1::load_bytes()).unwrap()]),
            &mut thread_rng(),
        )
        .unwrap();

        // Construct a PoSW proof.
        posw.mine(&mut block_header, &mut thread_rng()).unwrap();

        // Check that the difficulty target is satisfied.
        assert!(posw.verify(&block_header));

        // Check that the difficulty target is *not* satisfied.
        assert!(!posw.verify(&block_header));
    }

    /// TODO (howardwu): TEMPORARY - Move this up to the algorithms level of Merkle tree tests.
    #[test]
    fn test_changing_tx_roots() {
        use crate::{merkle_root_with_subroots, MerkleRoot};

        use anyhow::Result;

        /// Subtree calculation
        fn txids_to_roots<N: Network>(
            transaction_ids: &[[u8; 32]],
        ) -> Result<(MerkleRoot, N::BlockHeaderRoot, Vec<[u8; 32]>)> {
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

            let masked_root = snarkvm_algorithms::merkle_tree::MerkleTree::<N::BlockHeaderTreeParameters>::new(
                std::sync::Arc::new(N::block_header_tree_parameters().clone()),
                &subroots,
            )?
            .root()
            .clone();

            Ok((MerkleRoot(merkle_root_bytes.clone()), masked_root, subroots))
        }

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
