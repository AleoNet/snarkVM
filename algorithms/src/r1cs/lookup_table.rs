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

use indexmap::IndexMap;
use snarkvm_fields::Field;
use snarkvm_utilities::serialize::*;

const DEFAULT_KEY_SIZE: usize = 2;

#[derive(Clone, Debug)]
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

    pub fn lookup(&self, key: &[F]) -> Option<(usize, &[F; 2], &F)> {
        self.table.get_full(key)
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
