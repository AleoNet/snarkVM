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

impl<A: Aleo> Record<A, Plaintext<A>> {
    /// Returns the record commitment.
    pub fn to_commitment(&self) -> Field<A> {
        // Compute the BHP hash of the program record.
        A::hash_bhp1024(&self.to_bits_le())
    }
}

impl<A: Aleo> Record<A, Ciphertext<A>> {
    /// Returns the record commitment.
    pub fn to_commitment(&self) -> Field<A> {
        A::halt("Illegal operation: Record::to_commitment() cannot be invoked on the `Ciphertext` variant.")
    }
}
