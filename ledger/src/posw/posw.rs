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

use crate::{block::masked_merkle_root::MaskedMerkleRoot, posw::circuit::POSWCircuit, Network, PoswError};
use snarkvm_algorithms::{crh::sha256d_to_u64, traits::SNARK, SRS};
use snarkvm_dpc::Parameters;
use snarkvm_fields::ToConstraintField;
use snarkvm_parameters::{
    testnet1::{PoswSNARKPKParameters, PoswSNARKVKParameters},
    traits::Parameter,
};
use snarkvm_profiler::{end_timer, start_timer};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use blake2::{digest::Digest, Blake2s};
use rand::{CryptoRng, Rng};
use std::marker::PhantomData;

/// TODO (howardwu): Deprecate this function and use the implementation in `snarkvm-algorithms`.
/// Commits to the nonce and pedersen merkle root.
#[deprecated]
pub(super) fn commit(nonce: u32, root: &MaskedMerkleRoot) -> Vec<u8> {
    let mut h = Blake2s::new();
    h.update(&nonce.to_le_bytes());
    h.update(root.0.as_ref());
    h.finalize().to_vec()
}

/// A Proof of Succinct Work miner and verifier
#[derive(Clone)]
pub struct Posw<N: Network, const MASK_NUM_BYTES: usize> {
    /// The proving key. If not provided, the PoSW runner will work in verify-only
    /// mode and the `mine` function will panic.
    pub pk: Option<<<N as Network>::PoswSNARK as SNARK>::ProvingKey>,
    /// The (prepared) verifying key.
    pub vk: <<N as Network>::PoswSNARK as SNARK>::VerifyingKey,
    _circuit: PhantomData<POSWCircuit<N, MASK_NUM_BYTES>>,
}

impl<N: Network, const MASK_NUM_BYTES: usize> Posw<N, MASK_NUM_BYTES> {
    /// Loads the PoSW runner from the locally stored parameters.
    pub fn verify_only() -> Result<Self, PoswError> {
        let params = PoswSNARKVKParameters::load_bytes()?;
        let vk = <<N as Network>::PoswSNARK as SNARK>::VerifyingKey::read_le(&params[..])?;

        Ok(Self {
            pk: None,
            vk: vk.into(),
            _circuit: PhantomData,
        })
    }

    /// Loads the PoSW runner from the locally stored parameters.
    pub fn load() -> Result<Self, PoswError> {
        let vk =
            <<N as Network>::PoswSNARK as SNARK>::VerifyingKey::read_le(&PoswSNARKVKParameters::load_bytes()?[..])?;
        let pk = <<N as Network>::PoswSNARK as SNARK>::ProvingKey::read_le(&PoswSNARKPKParameters::load_bytes()?[..])?;

        Ok(Self {
            pk: Some(pk),
            vk: vk.into(),
            _circuit: PhantomData,
        })
    }

    /// Hashes the proof and checks it against the difficulty
    #[deprecated]
    fn check_difficulty(&self, proof: &[u8], difficulty_target: u64) -> bool {
        let hash_result = sha256d_to_u64(proof);
        hash_result <= difficulty_target
    }

    /// Performs a trusted setup for the PoSW circuit and returns an instance of the runner
    // TODO (howardwu): Find a workaround to keeping this method disabled.
    //  We need this method for benchmarking currently. There are two options:
    //  (1) Remove the benchmark for GM17 (since it is outdated anyways)
    //  (2) Update `Posw::setup` to take in an `OptionalRng` and account for the universal setup.
    // #[cfg(any(test, feature = "test-helpers"))]
    #[deprecated]
    pub fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, PoswError> {
        let params = <<N as Network>::PoswSNARK as SNARK>::setup(
            &POSWCircuit::<N, MASK_NUM_BYTES> {
                // the circuit will be padded internally
                hashed_leaves: vec![None; 0],
                mask: None,
                root: None,
            },
            &mut SRS::CircuitSpecific(rng),
        )?;

        Ok(Self {
            pk: Some(params.0),
            vk: params.1,
            _circuit: PhantomData,
        })
    }

    /// Performs a deterministic setup for systems with universal setups
    pub fn index<R: Rng + CryptoRng>(
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
            _circuit: PhantomData,
        })
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
        let pk = self.pk.as_ref().expect("tried to mine without a PK set up");

        let mut nonce;
        let mut proof;
        let mut serialized_proof;
        loop {
            nonce = rng.gen_range(0..max_nonce);
            proof = Self::prove(&pk, nonce, subroots, rng)?;

            serialized_proof = to_bytes_le!(proof)?;
            if self.check_difficulty(&serialized_proof, difficulty_target) {
                break;
            }
        }

        Ok((nonce, serialized_proof))
    }

    /// Runs the internal SNARK `prove` function on the POSW circuit and returns
    /// the proof serialized as bytes
    fn prove<R: Rng + CryptoRng>(
        pk: &<<N as Network>::PoswSNARK as SNARK>::ProvingKey,
        nonce: u32,
        subroots: &[[u8; 32]],
        rng: &mut R,
    ) -> Result<<<N as Network>::PoswSNARK as SNARK>::Proof, PoswError> {
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
        masked_merkle_root: &MaskedMerkleRoot,
    ) -> Result<(), PoswError> {
        // commit to it and the nonce
        let mask = commit(nonce, masked_merkle_root);

        // get the mask and the root in public inputs format
        let merkle_root = <N::DPC as Parameters>::InnerScalarField::read_le(&masked_merkle_root.0[..])?;
        let inputs = [mask.to_field_elements()?, vec![merkle_root]].concat();

        let res = <<N as Network>::PoswSNARK as SNARK>::verify(&self.vk, &inputs, &proof)?;
        if !res {
            return Err(PoswError::PoswVerificationFailed);
        }

        Ok(())
    }
}
