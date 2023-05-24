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

#[derive(Clone, PartialEq, Eq)]
pub struct VerifyingKey<N: Network> {
    /// The verifying key for the function.
    verifying_key: Arc<marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>>,
}

impl<N: Network> VerifyingKey<N> {
    /// Initializes a new verifying key.
    pub const fn new(
        verifying_key: Arc<marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>>,
    ) -> Self {
        Self { verifying_key }
    }

    /// Returns `true` if the proof is valid for the given public inputs.
    pub fn verify(&self, function_name: &str, inputs: &[N::Field], proof: &Proof<N>) -> bool {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Verify the proof.
        match Marlin::<N>::verify(N::marlin_fs_parameters(), self, inputs, proof) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                {
                    let elapsed = timer.elapsed().as_millis();
                    println!("{}", format!(" • Verified '{function_name}' (in {elapsed} ms)").dimmed());
                }

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
    pub fn verify_batch(&self, function_name: &str, inputs: &[Vec<N::Field>], proof: &Proof<N>) -> bool {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Verify the batch proof.
        let mut keys_to_inputs = BTreeMap::new();
        keys_to_inputs.insert(self.deref(), inputs);
        match Marlin::<N>::verify_batch(N::marlin_fs_parameters(), &keys_to_inputs, proof) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                {
                    let elapsed = timer.elapsed().as_millis();
                    println!("{}", format!(" • Verified '{function_name}' (in {elapsed} ms)").dimmed());
                }

                is_valid
            }
            Err(error) => {
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Verifier failed: {error}").dimmed());
                false
            }
        }
    }
}

impl<N: Network> Deref for VerifyingKey<N> {
    type Target = marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>;

    fn deref(&self) -> &Self::Target {
        &self.verifying_key
    }
}
