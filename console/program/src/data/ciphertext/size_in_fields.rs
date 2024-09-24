// Copyright 2024 Aleo Network Foundation
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

impl<N: Network> Visibility for Ciphertext<N> {
    type Boolean = Boolean<N>;

    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> Result<u16> {
        // Retrieve the number of field elements.
        let num_fields = self.0.len();
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match num_fields <= N::MAX_DATA_SIZE_IN_FIELDS as usize {
            // Return the number of field elements.
            true => Ok(u16::try_from(num_fields).or_halt_with::<N>("Ciphertext exceeds u16::MAX field elements.")),
            false => bail!("Ciphertext cannot exceed {} field elements.", N::MAX_DATA_SIZE_IN_FIELDS),
        }
    }
}
