// Copyright (C) 2019-2023 Aleo Systems Inc.
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
    pub(crate) const fn new(
        verifying_key: Arc<marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>>,
    ) -> Self {
        Self { verifying_key }
    }

    /// Returns `true` if the proof is valid for the given public inputs.
    pub fn verify(&self, function_name: &Identifier<N>, inputs: &[N::Field], proof: &Proof<N>) -> bool {
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
