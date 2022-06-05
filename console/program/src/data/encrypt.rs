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

impl<N: Network> Data<N, Plaintext<N>> {
    /// Encrypts `self` under the given Aleo address and randomizer.
    pub fn encrypt(&self, address: Address<N>, randomizer: N::Scalar) -> Result<Data<N, Ciphertext<N>>> {
        // Compute the data view key.
        let data_view_key = (*address * randomizer).to_affine().to_x_coordinate();
        // Encrypt the data.
        self.encrypt_symmetric(&data_view_key)
    }

    /// Encrypts `self` under the given data view key.
    pub fn encrypt_symmetric(&self, data_view_key: &N::Field) -> Result<Data<N, Ciphertext<N>>> {
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers =
            self.0.iter().map(|(_, value)| value.num_randomizers()).collect::<Result<Vec<_>>>()?.iter().sum();
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *data_view_key], num_randomizers);
        // Encrypt the data.
        let mut index: usize = 0;
        let mut encrypted_data = Vec::with_capacity(self.0.len());
        for (id, value, num_randomizers) in self.0.iter().map(|(id, value)| (id, value, value.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this value.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Encrypt the value, and add the value.
            encrypted_data.push((id.clone(), value.encrypt(randomizers)?));
            // Increment the index.
            index += num_randomizers;
        }
        Ok(Data(encrypted_data))
    }
}
