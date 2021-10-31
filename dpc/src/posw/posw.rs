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

use crate::{posw::PoSWCircuit, BlockHeader, Network, PoSWScheme, PoswError};
use core::sync::atomic::AtomicBool;
use snarkvm_algorithms::{crh::sha256d_to_u64, traits::SNARK, SRS};
use snarkvm_utilities::{FromBytes, ToBytes, UniformRand};

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
    /// Sets up an instance of PoSW using an SRS.
    fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoSWSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoswError> {
        let (proving_key, verifying_key) =
            <<N as Network>::PoSWSNARK as SNARK>::setup::<_, R>(&PoSWCircuit::<N>::blank()?, srs)?;

        Ok(Self {
            proving_key: Some(proving_key),
            verifying_key,
        })
    }

    /// Loads an instance of PoSW using stored parameters.
    fn load(is_prover: bool) -> Result<Self, PoswError> {
        Ok(Self {
            proving_key: match is_prover {
                true => Some(N::posw_proving_key().clone()),
                false => None,
            },
            verifying_key: N::posw_verifying_key().clone(),
        })
    }

    /// Returns a reference to the PoSW circuit proving key.
    fn proving_key(&self) -> &Option<<N::PoSWSNARK as SNARK>::ProvingKey> {
        &self.proving_key
    }

    /// Returns a reference to the PoSW circuit verifying key.
    fn verifying_key(&self) -> &<N::PoSWSNARK as SNARK>::VerifyingKey {
        &self.verifying_key
    }

    /// Given the leaves of the block header, it will calculate a PoSW and nonce
    /// such that they are under the difficulty target.
    fn mine<R: Rng + CryptoRng>(
        &self,
        block_header: &mut BlockHeader<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<(), PoswError> {
        let pk = self.proving_key.as_ref().expect("tried to mine without a PK set up");

        loop {
            // Sample a random nonce.
            block_header.set_nonce(UniformRand::rand(rng));

            // Instantiate the circuit.
            let circuit = PoSWCircuit::<N>::new(&block_header)?;

            // Generate the proof.
            block_header.set_proof(
                <<N as Network>::PoSWSNARK as SNARK>::prove_with_terminator(pk, &circuit, terminator, rng)?.into(),
            );

            if self.verify(block_header) {
                break;
            }
        }

        Ok(())
    }

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify(&self, block_header: &BlockHeader<N>) -> bool {
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
                if hash_difficulty > block_header.difficulty_target() {
                    eprintln!(
                        "PoSW difficulty target is not met. Expected {}, found {}",
                        block_header.difficulty_target(),
                        hash_difficulty
                    );
                    return false;
                }
            }
            Err(error) => {
                eprintln!("Failed to convert PoSW proof to bytes: {}", error);
                return false;
            }
        };

        // Construct the inputs.
        let inputs = vec![
            N::InnerScalarField::read_le(&block_header.to_header_root().unwrap().to_bytes_le().unwrap()[..]).unwrap(),
            block_header.nonce(),
        ];

        // Ensure the proof is valid.
        if !<<N as Network>::PoSWSNARK as SNARK>::verify(&self.verifying_key, &inputs, &*proof).unwrap() {
            eprintln!("PoSW proof verification failed");
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::AtomicBool;

    use crate::{testnet2::Testnet2, Network, PoSWScheme};
    use snarkvm_algorithms::{SNARK, SRS};
    use snarkvm_marlin::ahp::AHPForR1CS;
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
            let max_degree =
                AHPForR1CS::<<Testnet2 as Network>::InnerScalarField>::max_degree(20000, 20000, 200000).unwrap();
            let universal_srs =
                <<Testnet2 as Network>::PoSWSNARK as SNARK>::universal_setup(&max_degree, &mut thread_rng()).unwrap();
            <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::setup::<ThreadRng>(
                &mut SRS::<ThreadRng, _>::Universal(&universal_srs),
            )
            .unwrap()
        };

        // Construct a block header.
        let mut block_header = Testnet2::genesis_block().header().clone();
        posw.mine(&mut block_header, &AtomicBool::new(false), &mut thread_rng())
            .unwrap();

        assert!(block_header.proof().is_some());
        assert_eq!(
            block_header.proof().as_ref().unwrap().to_bytes_le().unwrap().len(),
            Testnet2::POSW_PROOF_SIZE_IN_BYTES
        ); // NOTE: Marlin proofs use compressed serialization
        assert!(posw.verify(&block_header));
    }
}
