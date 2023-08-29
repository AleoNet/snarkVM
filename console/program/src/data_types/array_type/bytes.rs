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

impl<N: Network> FromBytes for ArrayType<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the plaintext type.
        let plaintext_type = PlaintextType::read_le(&mut reader)?;
        // Read the length of the array.
        let length = U32::read_le(&mut reader)?;
        // Return the array type.
        Self::new(plaintext_type, length).map_err(|e| error(format!("{e}")))
    }
}

impl<N: Network> ToBytes for ArrayType<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the plaintext type.
        self.element_type().write_le(&mut writer)?;
        // Write the length of the array.
        self.length.write_le(&mut writer)
    }
}
