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

impl<A: Aleo> Record<A> {
    /// Returns the record commitment.
    pub fn to_commitment(&self) -> Field<A> {
        // TODO (howardwu): Abstraction - Replace data with an ID.
        let data = A::hash_bhp1024(&self.data.to_bits_le());

        // TODO (howardwu): Abstraction - add support for a custom BHP hash size.
        let left = A::hash_bhp1024(&[&self.program, &self.owner, &self.balance, &data].to_bits_le());
        let right = A::hash_bhp1024(&[&self.nonce, &self.mac, &self.bcm].to_bits_le());
        A::hash_bhp512(&[&left, &right].to_bits_le())
    }
}
