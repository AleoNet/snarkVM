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
    proving_key: Arc<varuna::CircuitProvingKey<N::PairingCurve, varuna::VarunaHidingMode>>,
}

impl<N: Network> ProvingKey<N> {
    /// Initializes a new proving key.
    pub const fn new(proving_key: Arc<varuna::CircuitProvingKey<N::PairingCurve, varuna::VarunaHidingMode>>) -> Self {
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

        // Retrieve the proving parameters.
        let universal_prover = N::varuna_universal_prover();
        let fiat_shamir = N::varuna_fs_parameters();

        // Compute the proof.
        let proof = Proof::new(Varuna::<N>::prove(universal_prover, fiat_shamir, self, assignment, rng)?);

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executed '{function_name}' (in {} ms)", timer.elapsed().as_millis()).dimmed());
        Ok(proof)
    }

    /// Returns a proof for the given batch of proving keys and assignments.
    #[allow(clippy::type_complexity)]
    pub fn prove_batch<'a, R: Rng + CryptoRng>(
        locator: &str,
        assignments: impl Iterator<Item = (&'a ProvingKey<N>, &'a [circuit::Assignment<N::Field>])>,
        rng: &mut R,
    ) -> Result<Proof<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Prepare the instances.
        let instances = assignments
            .map(|(proving_key, assignments)| (proving_key.deref(), assignments))
            .collect::<BTreeMap<_, _>>();

        // Retrieve the proving parameters.
        let universal_prover = N::varuna_universal_prover();
        let fiat_shamir = N::varuna_fs_parameters();

        // Compute the proof.
        let batch_proof = Proof::new(Varuna::<N>::prove_batch(universal_prover, fiat_shamir, &instances, rng)?);

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executed '{locator}' (in {} ms)", timer.elapsed().as_millis()).dimmed());

        Ok(batch_proof)
    }
}

impl<N: Network> Deref for ProvingKey<N> {
    type Target = varuna::CircuitProvingKey<N::PairingCurve, varuna::VarunaHidingMode>;

    fn deref(&self) -> &Self::Target {
        &self.proving_key
    }
}

impl<N: Network> Eq for ProvingKey<N> {}

impl<N: Network> PartialEq for ProvingKey<N> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<N: Network> Ord for ProvingKey<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other.deref())
    }
}

impl<N: Network> PartialOrd for ProvingKey<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
