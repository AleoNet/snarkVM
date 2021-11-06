// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::Network;
use snarkvm_algorithms::traits::EncryptionScheme;

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network"),
    Hash(bound = "N: Network")
)]
pub struct RecordViewKey<N: Network> {
    shared_secret: <N::RecordCiphertextScheme as EncryptionScheme>::SharedSecret,
    public_key: <N::RecordCiphertextScheme as EncryptionScheme>::PublicKey,
}

impl<N: Network> RecordViewKey<N> {
    pub fn new(
        shared_secret: <N::RecordCiphertextScheme as EncryptionScheme>::SharedSecret,
        public_key: <N::RecordCiphertextScheme as EncryptionScheme>::PublicKey,
    ) -> Self {
        Self {
            shared_secret,
            public_key,
        }
    }

    pub fn shared_secret(&self) -> &<N::RecordCiphertextScheme as EncryptionScheme>::SharedSecret {
        &self.shared_secret
    }

    pub fn public_key(&self) -> &<N::RecordCiphertextScheme as EncryptionScheme>::PublicKey {
        &self.public_key
    }
}
