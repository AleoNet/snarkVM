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

impl<N: Network, D: DataType> Data<N, D> {
    /// Encrypts `self` under the given Aleo address and randomizer,
    /// turning `self` into `Data::Ciphertext(..)` if the `mode` is private.
    /// Note: The output is guaranteed to satisfy `Data::is_valid(output)`.
    pub fn encrypt(&self, address: Address<N>, randomizer: N::Scalar) -> Result<Self> {
        match self {
            Self::Plaintext(data, Mode::Private) => {
                // Encode the data as field elements.
                let plaintext = Self::encode(data)?;
                // Compute the data view key.
                let data_view_key = (*address * randomizer).to_affine().to_x_coordinate();
                // Prepare a randomizer for each field element.
                let randomizers = N::hash_many_psd8(&[N::encryption_domain(), data_view_key], plaintext.len());
                // Compute the ciphertext field elements.
                let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| *p + r).collect();
                // Output the ciphertext.
                Ok(Self::Ciphertext(ciphertext, Mode::Private))
            }
            _ => Ok((*self).clone()),
        }
    }
}

impl<N: Network, D: DataType> Data<N, D> {
    /// Returns a list of field elements encoding the given data.
    pub(super) fn encode(data: &D) -> Result<Vec<N::Field>> {
        // Encode the data as little-endian bits.
        let mut bits = data.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits.push(true);
        // Pack the bits into field elements.
        bits.chunks(N::Field::size_in_data_bits())
            .map(|bits| {
                // Recover the base field.
                match N::Field::from_repr(<N::Field as PrimeField>::BigInteger::from_bits_le(bits)) {
                    // We know this case will always work, because we truncate the output to CAPACITY bits in the base field.
                    Some(field) => Ok(field),
                    _ => bail!("Failed to encode data bits into a base field"),
                }
            })
            .collect()
    }

    /// Returns the recovered data from encoded field elements.
    pub(super) fn decode(plaintext: &[N::Field]) -> D {
        // Unpack the field elements into bits, and reverse the list to pop the terminus bit off.
        let mut bits = plaintext.iter().flat_map(|p| p.to_bits_le()[..N::Field::size_in_data_bits()].to_vec()).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        D::from_bits_le(&bits.rev().collect::<Vec<_>>())
    }
}
