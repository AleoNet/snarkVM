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

impl<N: Network> Stack<N> {
    /// Returns a value for the given value type.
    pub fn sample_value<R: Rng + CryptoRng>(
        &self,
        burner_address: &Address<N>,
        value_type: &ValueType<N>,
        rng: &mut R,
    ) -> Result<Value<N>> {
        match value_type {
            ValueType::Constant(plaintext_type)
            | ValueType::Public(plaintext_type)
            | ValueType::Private(plaintext_type) => Ok(Value::Plaintext(self.sample_plaintext(plaintext_type, rng)?)),
            ValueType::Record(record_name) => {
                Ok(Value::Record(self.sample_record(burner_address, record_name, rng)?))
            }
            ValueType::ExternalRecord(locator) => {
                bail!("Illegal operation: Cannot sample external records (for '{locator}.record').")
            }
        }
    }

    /// Returns a record for the given record name, with the given burner address.
    pub fn sample_record<R: Rng + CryptoRng>(
        &self,
        burner_address: &Address<N>,
        record_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<Record<N, Plaintext<N>>> {
        // Sample a record.
        let record = self.sample_record_internal(burner_address, record_name, 0, rng)?;
        // Ensure the record matches the value type.
        self.matches_record(&record, record_name)?;
        // Return the record.
        Ok(record)
    }

    /// Samples a plaintext value according to the given plaintext type.
    pub fn sample_plaintext<R: Rng + CryptoRng>(
        &self,
        plaintext_type: &PlaintextType<N>,
        rng: &mut R,
    ) -> Result<Plaintext<N>> {
        // Sample a plaintext value.
        let plaintext = self.sample_plaintext_internal(plaintext_type, 0, rng)?;
        // Ensure the plaintext value matches the plaintext type.
        self.matches_plaintext(&plaintext, plaintext_type)?;
        // Return the plaintext value.
        Ok(plaintext)
    }
}

impl<N: Network> Stack<N> {
    /// Returns a record for the given record name.
    fn sample_record_internal<R: Rng + CryptoRng>(
        &self,
        burner_address: &Address<N>,
        record_name: &Identifier<N>,
        depth: usize,
        rng: &mut R,
    ) -> Result<Record<N, Plaintext<N>>> {
        // If the depth exceeds the maximum depth, then the plaintext type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Plaintext exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        // Retrieve the record type from the program.
        let record_type = self.program.get_record(record_name)?;

        // Initialize the owner based on the visibility.
        let owner = match record_type.owner().is_public() {
            true => RecordOwner::Public(*burner_address),
            false => RecordOwner::Private(Plaintext::Literal(Literal::Address(*burner_address), Default::default())),
        };

        // Initialize the record data according to the defined type.
        let data = record_type
            .entries()
            .iter()
            .map(|(entry_name, entry_type)| {
                // Sample the entry value.
                let entry = self.sample_entry_internal(entry_type, depth + 1, rng)?;
                // Return the entry.
                Ok((*entry_name, entry))
            })
            .collect::<Result<IndexMap<_, _>>>()?;

        // Initialize the nonce.
        let nonce = Group::rand(rng);

        // Return the record.
        Record::<N, Plaintext<N>>::from_plaintext(owner, data, nonce)
    }

    /// Samples an entry according to the given entry type.
    fn sample_entry_internal<R: Rng + CryptoRng>(
        &self,
        entry_type: &EntryType<N>,
        depth: usize,
        rng: &mut R,
    ) -> Result<Entry<N, Plaintext<N>>> {
        // If the depth exceeds the maximum depth, then the entry type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Entry exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        match entry_type {
            EntryType::Constant(plaintext_type)
            | EntryType::Public(plaintext_type)
            | EntryType::Private(plaintext_type) => {
                // Sample the plaintext value.
                let plaintext = self.sample_plaintext_internal(plaintext_type, depth, rng)?;
                // Return the entry.
                match entry_type {
                    EntryType::Constant(..) => Ok(Entry::Constant(plaintext)),
                    EntryType::Public(..) => Ok(Entry::Public(plaintext)),
                    EntryType::Private(..) => Ok(Entry::Private(plaintext)),
                }
            }
        }
    }

    /// Samples a plaintext value according to the given plaintext type.
    fn sample_plaintext_internal<R: Rng + CryptoRng>(
        &self,
        plaintext_type: &PlaintextType<N>,
        depth: usize,
        rng: &mut R,
    ) -> Result<Plaintext<N>> {
        // If the depth exceeds the maximum depth, then the plaintext type is invalid.
        ensure!(depth <= N::MAX_DATA_DEPTH, "Plaintext exceeded maximum depth of {}", N::MAX_DATA_DEPTH);

        // Sample the plaintext value.
        let plaintext = match plaintext_type {
            // Sample a literal.
            PlaintextType::Literal(literal_type) => {
                Plaintext::Literal(Literal::sample(*literal_type, rng), Default::default())
            }
            // Sample a struct.
            PlaintextType::Struct(struct_name) => {
                // Retrieve the struct.
                let struct_ = self.program.get_struct(struct_name)?;
                // Sample each member of the struct.
                let members = struct_
                    .members()
                    .iter()
                    .map(|(member_name, member_type)| {
                        // Sample the member value.
                        let member = self.sample_plaintext_internal(member_type, depth + 1, rng)?;
                        // Return the member.
                        Ok((*member_name, member))
                    })
                    .collect::<Result<IndexMap<_, _>>>()?;

                Plaintext::Struct(members, Default::default())
            }
        };
        // Return the plaintext.
        Ok(plaintext)
    }
}
