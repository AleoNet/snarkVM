// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

mod bytes;
mod parse;
mod serialize;

use std::collections::BTreeMap;

#[derive(Clone)]
pub struct ProvingKey<N: Network> {
    /// The proving key for the function.
    proving_key: Arc<marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>>,
}

impl<N: Network> ProvingKey<N> {
    /// Initializes a new proving key.
    pub const fn new(proving_key: Arc<marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>>) -> Self {
        Self { proving_key }
    }

    /// Returns a proof for the given assignment on the circuit.
    pub fn prove<R: Rng + CryptoRng>(
        &self,
        function_name: &str,
        assignment: &circuit::Assignment<N::Field>,
        rng: &mut R,
    ) -> Result<Proof<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Compute the proof.
        let proof = Proof::new(Marlin::<N>::prove(N::marlin_fs_parameters(), self, assignment, rng)?);

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executed '{function_name}' (in {} ms)", timer.elapsed().as_millis()).dimmed());
        Ok(proof)
    }

    /// Returns a proof for the given batch of assignments on the circuit.
    pub fn prove_batch<R: Rng + CryptoRng>(
        &self,
        function_name: &str,
        assignments: &[circuit::Assignment<N::Field>],
        rng: &mut R,
    ) -> Result<Proof<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Compute the batch proof.
        let mut assignment_refs: Vec<&circuit::Assignment<N::Field>> = vec![];
        for assignment in assignments {
            assignment_refs.push(assignment);
        }
        let mut keys_to_constraints = BTreeMap::new();
        keys_to_constraints.insert(self.deref(), assignment_refs.as_slice());
        let batch_proof = Proof::new(Marlin::<N>::prove_batch(N::marlin_fs_parameters(), &keys_to_constraints, rng)?);

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executed '{function_name}' (in {} ms)", timer.elapsed().as_millis()).dimmed());
        Ok(batch_proof)
    }
}

impl<N: Network> Deref for ProvingKey<N> {
    type Target = marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>;

    fn deref(&self) -> &Self::Target {
        &self.proving_key
    }
}
