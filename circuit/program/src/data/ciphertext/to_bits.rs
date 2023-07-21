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

impl<A: Aleo> ToBitsInto for Ciphertext<A> {
    type Boolean = Boolean<A>;

    /// Returns this ciphertext as a list of **little-endian** bits.
    fn to_bits_le_into(&self, vec: &mut Vec<Self::Boolean>) {
        let initial_len = vec.len();
        self.0.to_bits_le_into(vec);
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), vec.len() - initial_len);
    }

    /// Returns this ciphertext as a list of **big-endian** bits.
    fn to_bits_be_into(&self, vec: &mut Vec<Self::Boolean>) {
        let initial_len = vec.len();
        self.0.to_bits_be_into(vec);
        assert_eq!(self.0.len() * A::BaseField::size_in_bits(), vec.len() - initial_len);
    }
}
