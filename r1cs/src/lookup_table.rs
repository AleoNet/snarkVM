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

use indexmap::IndexMap;
use snarkvm_fields::Field;
use snarkvm_utilities::serialize::*;

const DEFAULT_KEY_SIZE: usize = 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupTable<F: Field> {
    pub table: IndexMap<[F; DEFAULT_KEY_SIZE], F>,
}

impl<F: Field> Default for LookupTable<F> {
    fn default() -> Self {
        Self { table: IndexMap::new() }
    }
}

impl<F: Field> LookupTable<F> {
    pub fn fill(&mut self, key: [F; DEFAULT_KEY_SIZE], val: F) -> Option<F> {
        self.table.insert(key, val)
    }

    pub fn lookup(&self, key: &[F]) -> Option<&F> {
        self.table.get(key)
    }
}

impl<F: Field> CanonicalSerialize for LookupTable<F> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: Compress) -> Result<(), SerializationError> {
        self.table.len().serialize_with_mode(&mut writer, compress)?;
        for (k, v) in self.table.iter() {
            for el in k {
                el.serialize_with_mode(&mut writer, compress)?;
            }
            v.serialize_with_mode(&mut writer, compress)?;
        }
        Ok(())
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        self.table.len().serialized_size(compress)
            + self.table.iter().map(|(k, v)| k.serialized_size(compress) + v.serialized_size(compress)).sum::<usize>()
    }
}

impl<F: Field> Valid for LookupTable<F> {
    fn check(&self) -> Result<(), SerializationError> {
        F::batch_check(self.table.keys().flatten().chain(self.table.values()))
    }
}

impl<F: Field> CanonicalDeserialize for LookupTable<F> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let mut table = IndexMap::new();
        let len = usize::deserialize_with_mode(&mut reader, compress, validate)?;
        for _ in 0..len {
            table.insert(
                {
                    let mut key = [F::zero(); DEFAULT_KEY_SIZE];
                    for el in key.iter_mut() {
                        *el = F::deserialize_with_mode(&mut reader, compress, validate)?;
                    }
                    key
                },
                F::deserialize_with_mode(&mut reader, compress, validate)?,
            );
        }
        Ok(Self { table })
    }
}
