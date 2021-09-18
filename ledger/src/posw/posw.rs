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
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use rand::{CryptoRng, Rng};

/// A Proof of Succinct Work miner and verifier
#[derive(Clone)]
pub struct Posw<N: Network, const MASK_NUM_BYTES: usize> {
    /// The proving key. If not provided, the PoSW runner will work in verify-only
    /// mode and the `mine` function will panic.
    pub pk: Option<<<N as Network>::PoswSNARK as SNARK>::ProvingKey>,
    /// The (prepared) verifying key.
    pub vk: <<N as Network>::PoswSNARK as SNARK>::VerifyingKey,
}

impl<N: Network, const MASK_NUM_BYTES: usize> Posw<N, MASK_NUM_BYTES> {
    /// Sets up an instance of PoSW using an SRS.
    pub fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoswSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoswError> {
        let params = <<N as Network>::PoswSNARK as SNARK>::setup::<_, R>(
            &POSWCircuit::<N, MASK_NUM_BYTES> {
                // the circuit will be padded internally
                hashed_leaves: vec![None; 0],
                mask: None,
                root: None,
            },
            srs,
        )?;

        Ok(Self {
            pk: Some(params.0),
            vk: params.1,
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

        Ok(Self { pk, vk: vk.into() })
    }

    /// Given the subroots of the block, it will calculate a POSW and a nonce such that they are
    /// under the difficulty target. These can then be used in the block header's field.
    pub fn mine<R: Rng + CryptoRng>(
        &self,
        subroots: &[[u8; 32]],
        difficulty_target: u64,
        rng: &mut R,
        max_nonce: u32,
    ) -> Result<(u32, Vec<u8>), PoswError> {
        let mut nonce;
        let mut proof;
        let mut serialized_proof;
        loop {
            nonce = rng.gen_range(0..max_nonce);
            proof = self.prove(nonce, subroots, rng)?;

            serialized_proof = to_bytes_le!(proof)?;
            if self.check_difficulty(&serialized_proof, difficulty_target) {
                break;
            }
        }

        Ok((nonce, serialized_proof))
    }

    /// Hashes the proof and checks it against the difficulty
    #[deprecated]
    fn check_difficulty(&self, proof: &[u8], difficulty_target: u64) -> bool {
        let hash_result = sha256d_to_u64(proof);
        hash_result <= difficulty_target
    }

    /// Runs the internal SNARK `prove` function on the POSW circuit and returns
    /// the proof serialized as bytes
    fn prove<R: Rng + CryptoRng>(
        &self,
        nonce: u32,
        subroots: &[[u8; 32]],
        rng: &mut R,
    ) -> Result<<<N as Network>::PoswSNARK as SNARK>::Proof, PoswError> {
        let pk = self.pk.as_ref().expect("tried to mine without a PK set up");

        // instantiate the circuit with the nonce
        let circuit = POSWCircuit::<N, MASK_NUM_BYTES>::new(nonce, subroots)?;

        // generate the proof
        let proof_timer = start_timer!(|| "POSW proof");
        let proof = <<N as Network>::PoswSNARK as SNARK>::prove(pk, &circuit, rng)?;
        end_timer!(proof_timer);

        Ok(proof)
    }

    /// Verifies the Proof of Succinct Work against the nonce and pedersen merkle
    /// root hash (produced by running a pedersen hash over the roots of the subtrees
    /// created by the block's transaction ids)
    pub fn verify(
        &self,
        nonce: u32,
        proof: &<<N as Network>::PoswSNARK as SNARK>::Proof,
        root: &N::PoswRoot,
    ) -> Result<(), PoswError> {
        // commit to it and the nonce
        let mask = POSWCircuit::<N, MASK_NUM_BYTES>::commit(nonce, root)?;

        // get the mask and the root in public inputs format
        let merkle_root = N::InnerScalarField::read_le(&root.to_bytes_le()?[..])?;
        let inputs = [mask.to_field_elements()?, vec![merkle_root]].concat();

        if !<<N as Network>::PoswSNARK as SNARK>::verify(&self.vk, &inputs, &proof)? {
            return Err(PoswError::PoswVerificationFailed);
        }

        Ok(())
    }
}
