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

use crate::{
    posw::PoSWCircuit,
    BlockHeader,
    BlockHeaderMetadata,
    BlockTemplate,
    Network,
    PoSWError,
    PoSWProof,
    PoSWScheme,
};
use snarkvm_algorithms::{crh::sha256d_to_u64, traits::SNARK, SRS};
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

use chrono::Utc;
use core::sync::atomic::AtomicBool;
use rand::{CryptoRng, Rng};

/// A Proof of Succinct Work miner and verifier.
#[derive(Clone)]
pub struct PoSW<N: Network> {
    /// The proving key. If not provided, PoSW will work in verify-only mode
    /// and the `mine` function will panic.
    proving_key: Option<<<N as Network>::PoSWSNARK as SNARK>::ProvingKey>,
    /// The verifying key.
    verifying_key: <<N as Network>::PoSWSNARK as SNARK>::VerifyingKey,
}

impl<N: Network> PoSWScheme<N> for PoSW<N> {
    ///
    /// Initializes a new instance of PoSW using the given SRS.
    ///
    fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoSWSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoSWError> {
        let (proving_key, verifying_key) =
            <<N as Network>::PoSWSNARK as SNARK>::setup::<_, R>(&PoSWCircuit::<N>::blank()?, srs)?;

        Ok(Self {
            proving_key: Some(proving_key),
            verifying_key,
        })
    }

    ///
    /// Loads an instance of PoSW using stored parameters.
    ///
    fn load(is_prover: bool) -> Result<Self, PoSWError> {
        Ok(Self {
            proving_key: match is_prover {
                true => Some(N::posw_proving_key().clone()),
                false => None,
            },
            verifying_key: N::posw_verifying_key().clone(),
        })
    }

    ///
    /// Returns a reference to the PoSW circuit proving key.
    ///
    fn proving_key(&self) -> &Option<<N::PoSWSNARK as SNARK>::ProvingKey> {
        &self.proving_key
    }

    ///
    /// Returns a reference to the PoSW circuit verifying key.
    ///
    fn verifying_key(&self) -> &<N::PoSWSNARK as SNARK>::VerifyingKey {
        &self.verifying_key
    }

    ///
    /// Given the block template, compute a PoSW and nonce that satisfies the difficulty target.
    ///
    fn mine<R: Rng + CryptoRng>(
        &self,
        block_template: &BlockTemplate<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<BlockHeader<N>, PoSWError> {
        const MAXIMUM_MINING_DURATION: i64 = 600; // 600 seconds = 10 minutes.

        // Instantiate the circuit.
        let mut circuit = PoSWCircuit::<N>::new(&block_template, UniformRand::rand(rng))?;

        let mut iteration = 1;
        let mut proof;
        loop {
            // Every 100 iterations, check that the miner is still within the allowed mining duration.
            if iteration % 100 == 0
                && Utc::now().timestamp() >= block_template.block_timestamp() + MAXIMUM_MINING_DURATION
            {
                return Err(PoSWError::Message("Failed mine block in the allowed mining duration".to_string()).into());
            }

            // Run one iteration of PoSW.
            proof = self.prove_once_unchecked(&mut circuit, block_template, terminator, rng)?;

            // Check if the updated block header is valid.
            if self.verify(
                block_template.block_height(),
                block_template.difficulty_target(),
                &circuit.to_public_inputs(),
                &proof,
            ) {
                // Construct a block header.
                let block_header = BlockHeader::from(
                    block_template.previous_ledger_root(),
                    block_template.transactions().transactions_root(),
                    BlockHeaderMetadata::new(block_template),
                    circuit.nonce(),
                    proof,
                )?;

                return Ok(block_header);
            }

            // Increment the iteration by one.
            iteration += 1;
        }
    }

    ///
    /// Given the block template, compute a PoSW proof.
    /// WARNING - This method does *not* ensure the resulting proof satisfies the difficulty target.
    ///
    fn prove_once_unchecked<R: Rng + CryptoRng>(
        &self,
        circuit: &mut PoSWCircuit<N>,
        block_template: &BlockTemplate<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<PoSWProof<N>, PoSWError> {
        let pk = self.proving_key.as_ref().expect("tried to mine without a PK set up");

        // Sample a random nonce.
        circuit.set_nonce(UniformRand::rand(rng));

        // TODO (raychu86): TEMPORARY - Remove this after testnet2 period.
        // Mine blocks with the deprecated PoSW mode for blocks behind `V12_UPGRADE_BLOCK_HEIGHT`.
        let proof = if <N as Network>::NETWORK_ID == 2
            && block_template.block_height() <= crate::testnet2::V12_UPGRADE_BLOCK_HEIGHT
        {
            let pk = <crate::testnet2::DeprecatedPoSWSNARK<N> as SNARK>::ProvingKey::from_bytes_le(&pk.to_bytes_le()?)?;
            // Construct a PoSW proof.
            PoSWProof::<N>::new_hiding(
                <crate::testnet2::DeprecatedPoSWSNARK<N> as SNARK>::prove_with_terminator(
                    &pk, circuit, terminator, rng,
                )?
                .into(),
            )
        } else {
            // Construct a PoSW proof.
            PoSWProof::<N>::new(
                <<N as Network>::PoSWSNARK as SNARK>::prove_with_terminator(pk, circuit, terminator, rng)?.into(),
            )
        };

        Ok(proof)
    }

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify_from_block_header(&self, block_header: &BlockHeader<N>) -> bool {
        self.verify(
            block_header.height(),
            block_header.difficulty_target(),
            &vec![*block_header.to_header_root().unwrap(), *block_header.nonce()],
            block_header.proof(),
        )
    }

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify(
        &self,
        block_height: u32,
        difficulty_target: u64,
        inputs: &Vec<N::InnerScalarField>,
        proof: &PoSWProof<N>,
    ) -> bool {
        // Ensure the difficulty target is met.
        match proof.to_bytes_le() {
            Ok(proof_bytes) => {
                let proof_difficulty = sha256d_to_u64(&proof_bytes);
                if proof_difficulty > difficulty_target {
                    #[cfg(debug_assertions)]
                    eprintln!(
                        "PoSW difficulty target is not met. Expected {}, found {}",
                        difficulty_target, proof_difficulty
                    );
                    return false;
                }
            }
            Err(error) => {
                eprintln!("Failed to convert PoSW proof to bytes: {}", error);
                return false;
            }
        };

        // TODO (raychu86): TEMPORARY - Remove this after testnet2 period.
        // Verify blocks with the deprecated PoSW mode for blocks behind `V12_UPGRADE_BLOCK_HEIGHT`.
        if <N as Network>::NETWORK_ID == 2 && block_height <= crate::testnet2::V12_UPGRADE_BLOCK_HEIGHT {
            // Ensure the proof type is hiding.
            if !proof.is_hiding() {
                eprintln!("[deprecated] PoSW proof for block {} should be hiding", block_height);
                return false;
            }
        }
        // Ensure the proof type is not hiding.
        else if proof.is_hiding() {
            eprintln!("PoSW proof for block {} should not be hiding", block_height);
            return false;
        }

        // Ensure the proof is valid under the deprecated PoSW parameters.
        if !proof.verify(&self.verifying_key, inputs) {
            eprintln!("PoSW proof verification failed");
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::AtomicBool;

    use crate::{testnet2::Testnet2, BlockTemplate, Network, PoSWScheme};
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_marlin::{ahp::AHPForR1CS, marlin::MarlinTestnet1Mode};
    use snarkvm_utilities::ToBytes;

    use rand::{rngs::ThreadRng, thread_rng};

    #[test]
    fn test_load() {
        let _params = <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::load(true).unwrap();
    }

    #[test]
    fn test_posw_marlin() {
        // Construct an instance of PoSW.
        let posw = {
            let max_degree = AHPForR1CS::<<Testnet2 as Network>::InnerScalarField, MarlinTestnet1Mode>::max_degree(
                20000, 20000, 200000,
            )
            .unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::setup::<ThreadRng>(
                &mut SRS::<ThreadRng, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct the block template.
        let block = Testnet2::genesis_block();
        let block_template = BlockTemplate::new(
            block.previous_block_hash(),
            block.height(),
            block.timestamp(),
            block.difficulty_target(),
            block.cumulative_weight(),
            block.previous_ledger_root(),
            block.transactions().clone(),
            block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
        );

        // Construct a block header.
        let block_header = posw
            .mine(&block_template, &AtomicBool::new(false), &mut thread_rng())
            .unwrap();

        assert_eq!(
            block_header.proof().to_bytes_le().unwrap().len(),
            Testnet2::HEADER_PROOF_SIZE_IN_BYTES
        ); // NOTE: Marlin proofs use compressed serialization
        assert!(posw.verify_from_block_header(&block_header));
    }
}
