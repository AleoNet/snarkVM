// Copyright 2024 Aleo Network Foundation
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

#[derive(Clone, PartialEq, Eq)]
pub struct VerifyingKey<N: Network> {
    /// The verifying key for the function.
    verifying_key: Arc<varuna::CircuitVerifyingKey<N::PairingCurve>>,
    /// The number of constant, public, and private variables for the circuit.
    num_variables: u64,
}

impl<N: Network> VerifyingKey<N> {
    /// Initializes a new verifying key.
    pub const fn new(verifying_key: Arc<varuna::CircuitVerifyingKey<N::PairingCurve>>, num_variables: u64) -> Self {
        Self { verifying_key, num_variables }
    }

    /// Returns the number of constant, public, and private variables for the circuit.
    pub fn num_variables(&self) -> u64 {
        self.num_variables
    }

    /// Returns `true` if the proof is valid for the given public inputs.
    pub fn verify(&self, function_name: &str, inputs: &[N::Field], proof: &Proof<N>) -> bool {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Retrieve the verification parameters.
        let universal_verifier = N::varuna_universal_verifier();
        let fiat_shamir = N::varuna_fs_parameters();

        // Verify the proof.
        match Varuna::<N>::verify(universal_verifier, fiat_shamir, self, inputs, proof) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                println!(
                    "{}",
                    format!(" • Verified '{function_name}' (in {} ms)", timer.elapsed().as_millis()).dimmed()
                );
                is_valid
            }
            Err(error) => {
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Verifier failed: {error}").dimmed());
                false
            }
        }
    }

    /// Returns `true` if the batch proof is valid for the given public inputs.
    #[allow(clippy::type_complexity)]
    pub fn verify_batch(
        locator: &str,
        inputs: Vec<(VerifyingKey<N>, Vec<Vec<N::Field>>)>,
        proof: &Proof<N>,
    ) -> Result<()> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Convert the instances.
        let num_expected_keys = inputs.len();
        let keys_to_inputs: BTreeMap<_, _> =
            inputs.iter().map(|(verifying_key, inputs)| (verifying_key.deref(), inputs.as_slice())).collect();
        ensure!(keys_to_inputs.len() == num_expected_keys, "Incorrect number of verifying keys for batch proof");

        // Retrieve the verification parameters.
        let universal_verifier = N::varuna_universal_verifier();
        let fiat_shamir = N::varuna_fs_parameters();

        // Verify the batch proof.
        match Varuna::<N>::verify_batch(universal_verifier, fiat_shamir, &keys_to_inputs, proof) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                println!(
                    "{}",
                    format!(" • Verified '{locator}': {is_valid} (in {} ms)", timer.elapsed().as_millis()).dimmed()
                );
                if is_valid { Ok(()) } else { bail!("'verify_batch' failed") }
            }
            Err(error) => {
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Verifier failed: {error}").dimmed());
                bail!(error)
            }
        }
    }
}

impl<N: Network> Deref for VerifyingKey<N> {
    type Target = varuna::CircuitVerifyingKey<N::PairingCurve>;

    fn deref(&self) -> &Self::Target {
        &self.verifying_key
    }
}
