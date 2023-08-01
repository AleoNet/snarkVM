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

impl<N: Network> ToBits for Signature<N> {
    /// Returns the little-endian bits of the signature.
    fn to_bits_le(&self) -> Vec<bool> {
        // Allocate the `bits_le` vector.
        let mut bits_le = Vec::with_capacity(Self::size_in_bits());
        // Write the challenge bits.
        bits_le.extend(self.challenge.to_bits_le());
        // Write the response bits.
        bits_le.extend(self.response.to_bits_le());
        // Write the compute key bits.
        bits_le.extend(self.compute_key.to_bits_le());
        // Return the `bits_le` vector.
        bits_le
    }

    /// Returns the big-endian bits of the signature.
    fn to_bits_be(&self) -> Vec<bool> {
        // Allocate the `bits_be` vector.
        let mut bits_be = Vec::with_capacity(Self::size_in_bits());
        // Write the challenge bits.
        bits_be.extend(self.challenge.to_bits_be());
        // Write the response bits.
        bits_be.extend(self.response.to_bits_be());
        // Write the compute key bits.
        bits_be.extend(self.compute_key.to_bits_be());
        // Return the `bits_be` vector.
        bits_be
    }
}

#[cfg(test)]
mod tests {

    // TODO
}
