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

impl<A: Aleo> ToBits for Ciphertext<A> {
    type Boolean = Boolean<A>;

    /// Returns this ciphertext as a list of **little-endian** bits.
    fn to_bits_le(&self) -> Vec<Self::Boolean> {
        let bits_le = self.0.to_bits_le();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_le.len());
        bits_le
    }

    /// Returns this ciphertext as a list of **big-endian** bits.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        let bits_be = self.0.to_bits_be();
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), bits_be.len());
        bits_be
    }
}
