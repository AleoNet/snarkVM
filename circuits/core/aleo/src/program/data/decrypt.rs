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

impl<A: Aleo> Data<A, Ciphertext<A>> {
    /// Decrypts `self` into plaintext using the given view key & nonce,
    pub fn decrypt(&self, view_key: Scalar<A>, nonce: Field<A>) -> Data<A, Plaintext<A>> {
        // Recover the nonce as a group.
        let nonce = Group::from_x_coordinate(nonce);
        // Compute the data view key.
        let data_view_key = (view_key * nonce).to_x_coordinate();
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers = self.0.iter().map(|(_, entry)| entry.num_randomizers()).sum();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], num_randomizers);
        // Decrypt the data.
        let mut index: usize = 0;
        let mut decrypted_data = Vec::with_capacity(self.0.len());
        for (id, entry, num_randomizers) in self.0.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Decrypt the entry, and add the entry.
            decrypted_data.push((id.clone(), entry.decrypt(randomizers)));
            // Increment the index.
            index += num_randomizers;
        }
        Data(decrypted_data)
    }
}
