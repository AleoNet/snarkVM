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

impl<A: Aleo> ToBits for Record<A, Plaintext<A>> {
    type Boolean = Boolean<A>;

    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // Compute the data bits.
        let data_bits_le = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| vec![identifier.to_bits_le(), entry.to_bits_le()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_le = self.owner.to_bits_le();
        bits_le.extend(self.balance.to_bits_le());
        bits_le.extend(U32::constant(console::U32::new(data_bits_le.len() as u32)).to_bits_le());
        bits_le.extend(data_bits_le);
        bits_le
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // Compute the data bits.
        let data_bits_be = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| vec![identifier.to_bits_be(), entry.to_bits_be()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_be = self.owner.to_bits_be();
        bits_be.extend(self.balance.to_bits_be());
        bits_be.extend(U32::constant(console::U32::new(data_bits_be.len() as u32)).to_bits_le());
        bits_be.extend(data_bits_be);
        bits_be
    }
}

impl<A: Aleo> ToBits for Record<A, Ciphertext<A>> {
    type Boolean = Boolean<A>;

    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        // Compute the data bits.
        let data_bits_le = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| vec![identifier.to_bits_le(), entry.to_bits_le()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_le = self.owner.to_bits_le();
        bits_le.extend(self.balance.to_bits_le());
        bits_le.extend(U32::constant(console::U32::new(data_bits_le.len() as u32)).to_bits_le());
        bits_le.extend(data_bits_le);
        bits_le
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        // Compute the data bits.
        let data_bits_be = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| vec![identifier.to_bits_be(), entry.to_bits_be()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_be = self.owner.to_bits_be();
        bits_be.extend(self.balance.to_bits_be());
        bits_be.extend(U32::constant(console::U32::new(data_bits_be.len() as u32)).to_bits_le());
        bits_be.extend(data_bits_be);
        bits_be
    }
}
