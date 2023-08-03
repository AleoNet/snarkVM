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

#[cfg(console)]
impl<A: Aleo> FromBits for Signature<A> {
    type Boolean = Boolean<A>;

    /// Initializes a new signature from a list of **little-endian** bits.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        let scalar_size_in_bits = console::Scalar::<A::Network>::size_in_bits();
        let compute_key_size_in_bits = console::ComputeKey::<A::Network>::size_in_bits();
        let (challenge_start, challenge_end) = (0, scalar_size_in_bits);
        let (response_start, response_end) = (challenge_end, challenge_end + scalar_size_in_bits);
        let (compute_key_start, compute_key_end) = (response_end, response_end + compute_key_size_in_bits);
        Self {
            challenge: Scalar::from_bits_le(&bits_le[challenge_start..challenge_end]),
            response: Scalar::from_bits_le(&bits_le[response_start..response_end]),
            compute_key: ComputeKey::from_bits_le(&bits_le[compute_key_start..compute_key_end]),
        }
    }

    /// Initializes a new signature from a list of **big-endian** bits.
    fn from_bits_be(bits_be: &[Self::Boolean]) -> Self {
        let scalar_size_in_bits = console::Scalar::<A::Network>::size_in_bits();
        let compute_key_size_in_bits = console::ComputeKey::<A::Network>::size_in_bits();
        let (challenge_start, challenge_end) = (0, scalar_size_in_bits);
        let (response_start, response_end) = (challenge_end, challenge_end + scalar_size_in_bits);
        let (compute_key_start, compute_key_end) = (response_end, response_end + compute_key_size_in_bits);
        Self {
            challenge: Scalar::from_bits_be(&bits_be[challenge_start..challenge_end]),
            response: Scalar::from_bits_be(&bits_be[response_start..response_end]),
            compute_key: ComputeKey::from_bits_be(&bits_be[compute_key_start..compute_key_end]),
        }
    }
}

#[cfg(all(test, console))]
mod tests {

    // TODO
}
