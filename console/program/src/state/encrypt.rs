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

impl<N: Network> State<N> {
    /// Returns a new record by encrypting this state using the view key of the **sender**,
    /// along with the given serial numbers and output index in the transition.
    pub fn encrypt<R: Rng + CryptoRng>(
        &self,
        view_key: &ViewKey<N>,
        serial_numbers: &[N::Field],
        output_index: u16,
        rng: &mut R,
    ) -> Result<Record<N>> {
        // Compute the encryption randomizer, which is bound to the account of the **sender**.
        let randomizer = Randomizer::prove(view_key, serial_numbers, output_index, rng)?;

        // Ensure the nonce corresponds to the given randomizer: `nonce == randomizer * G`.
        if self.nonce.to_projective() != N::g_scalar_multiply(randomizer.value()) {
            bail!("Found an invalid encryption randomizer for encrypting program state")
        }

        // Compute the record view key.
        let record_view_key = ((*self.owner).to_projective() * *randomizer.value()).to_affine().to_x_coordinate();
        // Encrypt the record and output the state.
        Record::encrypt(self, &record_view_key)
    }
}
