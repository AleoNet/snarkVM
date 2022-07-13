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

impl<A: Aleo> Identifier<A> {
    /// Returns the number of bits of this identifier.
    pub fn size_in_bits(&self) -> U8<A> {
        match self.1.checked_mul(8) {
            Some(num_bits) => U8::constant(console::U8::new(num_bits)),
            None => A::halt("Identifier exceeds maximum allowed size"),
        }
    }
}
