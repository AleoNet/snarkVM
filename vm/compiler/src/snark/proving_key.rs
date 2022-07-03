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

use super::*;

pub struct ProvingKey<N: Network> {
    /// The proving key for the function.
    proving_key: marlin::CircuitProvingKey<Bls12_377, marlin::MarlinHidingMode>,
    /// PhantomData
    _phantom: PhantomData<N>,
}

impl<N: Network> ProvingKey<N> {
    /// Initializes a new proving key.
    pub(super) const fn new(proving_key: marlin::CircuitProvingKey<Bls12_377, marlin::MarlinHidingMode>) -> Self {
        Self { proving_key, _phantom: PhantomData }
    }

    /// Returns a proof for the given assignment on the circuit.
    fn prove<R: Rng + CryptoRng>(&self, assignment: circuit::Assignment<Fr>, rng: &mut R) -> Result<Proof<N>> {
        let timer = std::time::Instant::now();
        let proof = Proof::new(Marlin::prove_batch(self, std::slice::from_ref(&assignment), rng)?);
        println!("Called prover: {} ms", timer.elapsed().as_millis());
        Ok(proof)
    }
}

impl<N: Network> Deref for ProvingKey<N> {
    type Target = marlin::CircuitProvingKey<Bls12_377, marlin::MarlinHidingMode>;

    fn deref(&self) -> &Self::Target {
        &self.proving_key
    }
}
