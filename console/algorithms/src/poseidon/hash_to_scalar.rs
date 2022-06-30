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

impl<E: Environment, const RATE: usize> HashToScalar for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Scalar<E>;

    /// Returns a scalar from hashing the input.
    /// This method uses truncation (up to data bits) to project onto the scalar field.
    #[inline]
    fn hash_to_scalar(&self, input: &[Self::Input]) -> Result<Self::Output> {
        // Note: We are reconstituting the base field into a scalar field.
        // This is safe as the scalar field modulus is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(Scalar::<E>::size_in_bits() < Field::<E>::size_in_bits());

        // Hash the input to the base field.
        let output = self.hash(input)?;

        // Truncate the output to the size in data bits (1 bit less than the MODULUS) of the scalar.
        // Slicing here is safe as the base field is larger than the scalar field.
        let bits = &output.to_bits_le()[..Scalar::<E>::size_in_data_bits()];

        // Output the scalar.
        Scalar::from_bits_le(bits)
    }
}
