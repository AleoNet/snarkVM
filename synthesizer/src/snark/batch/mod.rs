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

use circuit::Assignment;
use std::collections::BTreeMap;

#[derive(Clone, PartialEq, Eq)]
pub enum Key<N: Network> {
    ProvingKey(ProvingKey<N>),
    VerifyingKey(VerifyingKey<N>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum KeyMode {
    Proving = 0,
    Verifying = 1,
}

#[derive(Clone)]
pub struct KeyBatch<N: Network> {
    /// A batch of proving or verifying keys
    batch: Vec<Key<N>>,
    mode: KeyMode,
}

impl<N: Network> KeyBatch<N> {
    /// Initializes a new batch.
    pub(crate) fn new(keys: usize, mode: KeyMode) -> Self {
        Self { batch: Vec::with_capacity(keys), mode }
    }

    /// Adds keys to the batch.
    pub(crate) fn add(&mut self, key: Key<N>) -> Result<(), anyhow::Error> {
        match key {
            Key::VerifyingKey(_) => {
                if matches!(self.mode, KeyMode::Proving) {
                    bail!("Cannot add a verifying key to a proving batch")
                }
            }
            Key::ProvingKey(_) => {
                if matches!(self.mode, KeyMode::Verifying) {
                    bail!("Cannot add a proving key to a verifying batch")
                }
            }
        }
        self.batch.push(key);
        Ok(())
    }

    /// Returns a proof for the given batch of assignments on the batch of circuits.
    pub fn prove<R: Rng + CryptoRng>(
        &self,
        function_names: &[&Identifier<N>],
        assignments: &[&Vec<&Assignment<N::Field>>],
        proves_inclusion: bool,
        rng: &mut R,
    ) -> Result<Proof<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        let mut keys_to_constraints = BTreeMap::new();
        for (key, &circuit_assignments) in self.batch.iter().zip(assignments) {
            match key {
                Key::VerifyingKey(_) => {
                    bail!("Cannot use a verifying key to prove a batch")
                }
                Key::ProvingKey(pk) => {
                    keys_to_constraints.insert(pk.deref(), circuit_assignments.as_slice());
                }
            }
        }

        // Compute the batch proof.
        let batch_proof = Proof::new(
            Marlin::<N>::prove_batch(N::marlin_fs_parameters(), &keys_to_constraints, rng)?,
            proves_inclusion,
        );

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executed '{:?}' (in {} ms)", function_names, timer.elapsed().as_millis()).dimmed());
        Ok(batch_proof)
    }

    /// Returns `true` if the batch proof is valid for the given public inputs.
    pub fn verify(
        &self,
        function_names: &[&Identifier<N>],
        inputs: &[Vec<Vec<N::Field>>],
        proof: &Proof<N>,
    ) -> Result<()> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Verify the batch proof.
        let mut keys_to_inputs = BTreeMap::new();
        for (key, circuit_inputs) in self.batch.iter().zip(inputs) {
            match key {
                Key::VerifyingKey(vk) => {
                    keys_to_inputs.insert(vk.deref(), circuit_inputs.as_slice());
                }
                Key::ProvingKey(_) => {
                    bail!("Cannot use a proving key to verify a batch")
                }
            }
        }
        match Marlin::<N>::verify_batch(N::marlin_fs_parameters(), &keys_to_inputs, proof) {
            Ok(_is_valid) => {
                #[cfg(feature = "aleo-cli")]
                {
                    let elapsed = timer.elapsed().as_millis();
                    println!("{}", format!(" • Verified '{:?}' (in {elapsed} ms)", function_names).dimmed());
                }

                Ok(())
            }
            Err(error) => {
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Verifier failed: {error}").dimmed());
                Err(error.into())
            }
        }
    }
}
