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

use core::sync::atomic::AtomicBool;

use crate::{BlockHeader, Network, PoswError};
use snarkvm_algorithms::{traits::SNARK, SRS};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait PoSWScheme<N: Network>: Clone + Send + Sync {
    /// Sets up an instance of PoSW using an SRS.
    fn setup<R: Rng + CryptoRng>(
        srs: &mut SRS<R, <<N as Network>::PoswSNARK as SNARK>::UniversalSetupParameters>,
    ) -> Result<Self, PoswError>;

    /// Loads an instance of PoSW using stored parameters.
    fn load(is_prover: bool) -> Result<Self, PoswError>;

    /// Returns a reference to the PoSW circuit proving key.
    fn proving_key(&self) -> &Option<<N::PoswSNARK as SNARK>::ProvingKey>;

    /// Returns a reference to the PoSW circuit verifying key.
    fn verifying_key(&self) -> &<N::PoswSNARK as SNARK>::VerifyingKey;

    /// Given the leaves of the block header, it will calculate a PoSW and nonce
    /// such that they are under the difficulty target.
    fn mine<R: Rng + CryptoRng>(
        &self,
        block_header: &mut BlockHeader<N>,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<(), PoswError>;

    /// Verifies the Proof of Succinct Work against the nonce, root, and difficulty target.
    fn verify(&self, block_header: &BlockHeader<N>) -> bool;
}
