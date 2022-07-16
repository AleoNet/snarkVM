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

mod bytes;
mod parse;
mod serialize;

#[derive(Clone, PartialEq, Eq)]
pub struct VerifyingKey<N: Network> {
    /// The verifying key for the function.
    verifying_key: marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>,
}

impl<N: Network> VerifyingKey<N> {
    /// Initializes a new verifying key.
    pub(super) const fn new(
        verifying_key: marlin::CircuitVerifyingKey<N::PairingCurve, marlin::MarlinHidingMode>,
    ) -> Self {
        Self { verifying_key }
    }

    /// Returns `true` if the proof is valid for the given public inputs.
    pub fn verify(&self, function_name: &Identifier<N>, inputs: &[N::Field], proof: &Proof<N>) -> bool {
        let timer = std::time::Instant::now();
        match Marlin::<N>::verify_batch(self, std::slice::from_ref(&inputs), proof) {
            Ok(is_valid) => {
                let elapsed = timer.elapsed().as_millis();
                println!("{}", format!(" • Verified '{function_name}' (in {} ms)", elapsed).dimmed());
                is_valid
            }
            Err(error) => {
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
