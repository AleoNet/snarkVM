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

impl<N: Network> Record<N> {
    /// Returns the serial number of the record, given the private key of the record owner and an RNG.
    pub fn to_serial_number<R: Rng + CryptoRng>(
        &self,
        sk_sig: &N::Scalar,
        pr_sig: &N::Affine,
        message: &[N::Field],
        rng: &mut R,
    ) -> Result<SerialNumber<N>> {
        // Compute the serial number.
        SerialNumber::<N>::sign(&sk_sig, pr_sig, message, self.to_commitment()?, rng)
    }
}
