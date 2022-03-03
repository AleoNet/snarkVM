// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use core::sync::atomic::AtomicBool;

use crate::{BlockHeader, BlockTemplate, Network, PoSWCircuit, PoSWError, PoSWProof};
use snarkvm_algorithms::{traits::SNARK, SRS};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait PoSWScheme<N: Network>: Clone + Send + Sync {
    /// Sets up an instance of PoSW using an SRS.
    fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoSWSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoSWError>;

    /// Loads an instance of PoSW using stored parameters.
    fn load(is_prover: bool) -> Result<Self, PoSWError>;

    /// Returns a reference to the PoSW circuit proving key.
    fn proving_key(&self) -> &Option<<N::PoSWSNARK as SNARK>::ProvingKey>;

    /// Returns a reference to the PoSW circuit verifying key.
    fn verifying_key(&self) -> &<N::PoSWSNARK as SNARK>::VerifyingKey;

    /// Given the block template, compute a PoSW proof and nonce
    /// such that they are under the difficulty target.
    fn mine<R: Rng + CryptoRng>(
        &self,
        block_template: &BlockTemplate<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<BlockHeader<N>, PoSWError>;

    ///
    /// Given the block template, compute a PoSW proof.
    /// WARNING - This method does *not* ensure the resulting proof satisfies the difficulty target.
    ///
    fn prove_once_unchecked<R: Rng + CryptoRng>(
        &self,
        circuit: &mut PoSWCircuit<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<PoSWProof<N>, PoSWError>;

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify_from_block_header(&self, block_header: &BlockHeader<N>) -> bool;

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify(&self, difficulty_target: u64, inputs: &[N::InnerScalarField], proof: &PoSWProof<N>) -> bool;
}
