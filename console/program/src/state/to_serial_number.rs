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
    /// Returns the serial number of the record, given the private key of the state owner and an RNG.
    pub fn to_serial_number<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        rng: &mut R,
    ) -> Result<SerialNumber<N>> {
        // Ensure the private key belongs to the owner of the program state.
        ensure!(self.owner == private_key.try_into()?, "The private key does not match this program state");
        // Compute the program state digest.
        let state_digest = self.to_digest()?;
        // Compute the serial number.
        SerialNumber::<N>::prove(&private_key.sk_vrf(), state_digest, rng)
    }
}
