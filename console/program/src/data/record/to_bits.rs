// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> ToBits for Record<N, Plaintext<N>> {
    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        // Compute the data bits.
        let data_bits_le = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| [identifier.to_bits_le(), entry.to_bits_le()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_le = self.owner.to_bits_le();
        bits_le.extend(
            u32::try_from(data_bits_le.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_le(),
        );
        bits_le.extend(data_bits_le);
        bits_le.extend(self.nonce.to_bits_le());
        bits_le
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        // Compute the data bits.
        let data_bits_be = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| [identifier.to_bits_be(), entry.to_bits_be()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_be = self.owner.to_bits_be();
        bits_be.extend(
            u32::try_from(data_bits_be.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_be(),
        );
        bits_be.extend(data_bits_be);
        bits_be.extend(self.nonce.to_bits_be());
        bits_be
    }
}

impl<N: Network> ToBits for Record<N, Ciphertext<N>> {
    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<bool> {
        // Compute the data bits.
        let data_bits_le = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| [identifier.to_bits_le(), entry.to_bits_le()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_le = self.owner.to_bits_le();
        bits_le.extend(
            u32::try_from(data_bits_le.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_le(),
        );
        bits_le.extend(data_bits_le);
        bits_le.extend(self.nonce.to_bits_le());
        bits_le
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<bool> {
        // Compute the data bits.
        let data_bits_be = self
            .data
            .iter()
            .flat_map(|(identifier, entry)| [identifier.to_bits_be(), entry.to_bits_be()])
            .flatten()
            .collect::<Vec<_>>();

        // Construct the record bits.
        let mut bits_be = self.owner.to_bits_be();
        bits_be.extend(
            u32::try_from(data_bits_be.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_be(),
        );
        bits_be.extend(data_bits_be);
        bits_be.extend(self.nonce.to_bits_be());
        bits_be
    }
}
