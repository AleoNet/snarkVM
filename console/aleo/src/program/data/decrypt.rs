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
    /// Decrypts `self` into plaintext using the given view key & nonce,
    /// turning `Data::Ciphertext(..)` into `Data::Plaintext(..)`.
    /// Note: The output does **not** necessarily satisfy `Data::is_valid(output)`.
    pub fn decrypt(&self, view_key: ViewKey<N>, nonce: N::Field) -> Result<Self> {
        match self {
            Self::Plaintext(..) => Ok((*self).clone()),
            Self::Ciphertext(ciphertext, mode) => {
                // Recover the nonce as a group.
                let nonce = N::affine_from_x_coordinate(nonce)?.to_projective();
                // Compute the data view key.
                let data_view_key = (nonce * *view_key).to_affine().to_x_coordinate();
                // Prepare a randomizer for each field element.
                let randomizers = N::hash_many_psd8(&[N::encryption_domain(), data_view_key], ciphertext.len());
                // Compute the plaintext field elements.
                let plaintext: Vec<_> = ciphertext.iter().zip_eq(randomizers).map(|(c, r)| *c - r).collect();
                // Decode the data from field elements, and output the plaintext.
                Ok(Self::Plaintext(Self::decode(&plaintext), *mode))
            }
        }
    }
}
