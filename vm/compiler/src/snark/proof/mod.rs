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
pub struct Proof<N: Network> {
    /// The proof.
    proof: marlin::Proof<N::PairingCurve>,
}

impl<N: Network> Proof<N> {
    /// Initializes a new proof.
    pub(super) const fn new(proof: marlin::Proof<N::PairingCurve>) -> Self {
        Self { proof }
    }
}

impl<N: Network> Deref for Proof<N> {
    type Target = marlin::Proof<N::PairingCurve>;

    fn deref(&self) -> &Self::Target {
        &self.proof
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

    pub(super) fn sample_proof() -> Proof<CurrentNetwork> {
        static INSTANCE: OnceCell<Proof<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Sample a transition.
                let transition = crate::process::test_helpers::sample_transition();
                // Return the proof.
                transition.proof().clone()
            })
            .clone()
    }
}
