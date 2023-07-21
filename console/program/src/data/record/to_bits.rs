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

use snarkvm_utilities::ToBitsInto;

impl<N: Network> ToBitsInto for Record<N, Plaintext<N>> {
    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        // Compute the data bits.
        let mut data_bits_le = vec![];
        for (identifier, entry) in &self.data {
            identifier.to_bits_le_into(&mut data_bits_le);
            entry.to_bits_le_into(&mut data_bits_le);
        }

        // Construct the record bits.
        self.owner.to_bits_le_into(vec);
        u32::try_from(data_bits_le.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_le_into(vec);
        vec.extend_from_slice(&data_bits_le);
        self.nonce.to_bits_le_into(vec);
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        // Compute the data bits.
        let mut data_bits_be = vec![];
        for (identifier, entry) in &self.data {
            identifier.to_bits_be_into(&mut data_bits_be);
            entry.to_bits_be_into(&mut data_bits_be);
        }

        // Construct the record bits.
        self.owner.to_bits_be_into(vec);
        u32::try_from(data_bits_be.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_be_into(vec);
        vec.extend_from_slice(&data_bits_be);
        self.nonce.to_bits_be_into(vec);
    }
}

impl<N: Network> ToBitsInto for Record<N, Ciphertext<N>> {
    /// Returns this data as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<bool>) {
        // Compute the data bits.
        let mut data_bits_le = vec![];
        for (identifier, entry) in &self.data {
            identifier.to_bits_le_into(&mut data_bits_le);
            entry.to_bits_le_into(&mut data_bits_le);
        }

        // Construct the record bits.
        self.owner.to_bits_le_into(vec);
        u32::try_from(data_bits_le.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_le_into(vec);
        vec.extend_from_slice(&data_bits_le);
        self.nonce.to_bits_le_into(vec);
    }

    /// Returns this data as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<bool>) {
        // Compute the data bits.
        let mut data_bits_be = vec![];
        for (identifier, entry) in &self.data {
            identifier.to_bits_be_into(&mut data_bits_be);
            entry.to_bits_be_into(&mut data_bits_be);
        }

        // Construct the record bits.
        self.owner.to_bits_be_into(vec);
        u32::try_from(data_bits_be.len()).or_halt_with::<N>("Record data exceeds u32::MAX bits").to_bits_be_into(vec);
        vec.extend_from_slice(&data_bits_be);
        self.nonce.to_bits_be_into(vec);
    }
}
