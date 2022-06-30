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

impl<E: Environment, const RATE: usize> HashMany for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Field<E>;

    /// Returns the cryptographic hash for a list of field elements as input,
    /// and returns the specified number of field elements as output.
    #[inline]
    fn hash_many(&self, input: &[Self::Input], num_outputs: u16) -> Vec<Self::Output> {
        // Construct the preimage: [ DOMAIN || LENGTH(INPUT) || [0; RATE-2] || INPUT ].
        let mut preimage = Vec::with_capacity(RATE + input.len());
        preimage.push(self.domain);
        preimage.push(Field::<E>::from_u128(input.len() as u128));
        preimage.extend(&vec![Field::<E>::zero(); RATE - 2]); // Pad up to RATE.
        preimage.extend_from_slice(input);

        let mut sponge = PoseidonSponge::<E, RATE, CAPACITY>::new(&self.parameters);
        sponge.absorb(&preimage);
        sponge.squeeze(num_outputs).to_vec()
    }
}
