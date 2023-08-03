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
impl<A: Aleo> ToFields for Signature<A> {
    type Field = Field<A>;

    /// Casts a string into a list of base fields.
    fn to_fields(&self) -> Vec<Self::Field> {
        // Convert the string bytes into bits, then chunk them into lists of size
        // `E::BaseField::size_in_data_bits()` and recover the base field element for each chunk.
        // (For advanced users: Chunk into CAPACITY bits and create a linear combination per chunk.)
        self.to_bits_le().chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }
}

#[cfg(all(test, console))]
mod tests {

    // TODO
}
