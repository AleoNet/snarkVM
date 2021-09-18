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

use crate::{posw::circuit::POSWCircuit, PoswError};
use snarkvm_algorithms::{crh::sha256d_to_u64, traits::SNARK, SRS};
use snarkvm_dpc::Network;
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
pub struct Posw<N: Network, const MASK_NUM_BYTES: usize> {
    /// The proving key. If not provided, the PoSW runner will work in verify-only
    /// mode and the `mine` function will panic.
    pub proving_key: Option<<<N as Network>::PoswSNARK as SNARK>::ProvingKey>,
    /// The verifying key.
    pub verifying_key: <<N as Network>::PoswSNARK as SNARK>::VerifyingKey,
}

impl<N: Network, const MASK_NUM_BYTES: usize> Posw<N, MASK_NUM_BYTES> {
    /// Sets up an instance of PoSW using an SRS.
    pub fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoswSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoswError> {
        let (proving_key, verifying_key) =
            <<N as Network>::PoswSNARK as SNARK>::setup::<_, R>(&POSWCircuit::<N, MASK_NUM_BYTES>::blank()?, srs)?;

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

    /// Given the leaves of the block header, it will calculate a PoSW and nonce
    /// such that they are under the difficulty target.
    pub fn mine<R: Rng + CryptoRng>(
        &self,
        leaves: &[[u8; 32]],
        difficulty_target: u64,
        rng: &mut R,
        max_nonce: u32,
    ) -> Result<(u32, <<N as Network>::PoswSNARK as SNARK>::Proof), PoswError> {
        let mut nonce;
        let mut proof;
        loop {
            nonce = rng.gen_range(0..max_nonce);
            proof = self.prove(nonce, leaves, rng)?;

            if self.check_difficulty(&proof, difficulty_target) {
                break;
            }
        }

        Ok((nonce, proof))
    }

    /// Runs the SNARK `prove` function on the PoSW circuit and returns the proof.
    fn prove<R: Rng + CryptoRng>(
        &self,
        nonce: u32,
        leaves: &[[u8; 32]],
        rng: &mut R,
    ) -> Result<<<N as Network>::PoswSNARK as SNARK>::Proof, PoswError> {
        let pk = self.proving_key.as_ref().expect("tried to mine without a PK set up");

        // Instantiate the circuit with the nonce.
        let circuit = POSWCircuit::<N, MASK_NUM_BYTES>::new(nonce, leaves)?;

        // Generate the proof.
        let proof_timer = start_timer!(|| "PoSW proof");
        let proof = <<N as Network>::PoswSNARK as SNARK>::prove(pk, &circuit, rng)?;
        end_timer!(proof_timer);

        Ok(proof)
    }

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    pub fn verify(
        &self,
        nonce: u32,
        root: &N::PoswRoot,
        difficulty_target: u64,
        proof: &<<N as Network>::PoswSNARK as SNARK>::Proof,
    ) -> bool {
        let inputs = |(nonce, root): (u32, &N::PoswRoot)| -> anyhow::Result<Vec<N::InnerScalarField>> {
            // Commit to the nonce and root.
            let mask = POSWCircuit::<N, MASK_NUM_BYTES>::commit(nonce, root)?;

            // get the mask and the root in public inputs format
            let merkle_root = N::InnerScalarField::read_le(&root.to_bytes_le()?[..])?;
            let inputs = [mask.to_field_elements()?, vec![merkle_root]].concat();
            Ok(inputs)
        };

        // Construct the inputs.
        let inputs = match inputs((nonce, root)) {
            Ok(inputs) => inputs,
            Err(error) => {
                eprintln!("{}", error);
                return false;
            }
        };

        // Ensure the proof is valid.
        if !<<N as Network>::PoswSNARK as SNARK>::verify(&self.verifying_key, &inputs, &proof).unwrap() {
            eprintln!("PoSW proof verification failed");
            return false;
        }

        // Ensure the difficulty target is met.
        if !self.check_difficulty(proof, difficulty_target) {
            eprintln!("PoSW difficulty target is not met");
            return false;
        }

        true
    }

    /// Hashes the proof and checks it against the difficulty.
    pub fn check_difficulty(
        &self,
        proof: &<<N as Network>::PoswSNARK as SNARK>::Proof,
        difficulty_target: u64,
    ) -> bool {
        let hash_result = sha256d_to_u64(&proof.to_bytes_le().unwrap());
        hash_result <= difficulty_target
    }
}
