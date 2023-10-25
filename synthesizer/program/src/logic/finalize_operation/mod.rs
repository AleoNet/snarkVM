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

mod bits;
mod bytes;
mod serialize;
mod string;

use console::{network::prelude::*, types::Field};

/// Enum to represent the allowed set of Merkle tree operations.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum FinalizeOperation<N: Network> {
    /// Appends a mapping to the program tree, as (`mapping ID`).
    InitializeMapping(Field<N>),
    /// Inserts a key-value leaf into the mapping tree,
    /// as (`mapping ID`, `key ID`, `value ID`).
    InsertKeyValue(Field<N>, Field<N>, Field<N>),
    /// Updates the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`, `key ID`, `value ID`).
    UpdateKeyValue(Field<N>, u64, Field<N>, Field<N>),
    /// Removes the key-value leaf at the given index in the mapping tree,
    /// as (`mapping ID`, `index`).
    RemoveKeyValue(Field<N>, u64),
    /// Replaces a mapping from the program tree, as (`mapping ID`).
    ReplaceMapping(Field<N>),
    /// Removes a mapping from the program tree, as (`mapping ID`).
    RemoveMapping(Field<N>),
}

#[cfg(any(test, feature = "test-helpers"))]
pub mod test_helpers {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    /// Samples a random `InitializeMapping`.
    pub fn sample_initialize_mapping(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::InitializeMapping(Uniform::rand(rng))
    }

    /// Samples a random `InsertKeyValue`.
    pub fn sample_insert_key_value(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::InsertKeyValue(Uniform::rand(rng), Uniform::rand(rng), Uniform::rand(rng))
    }

    /// Samples a random `UpdateKeyValue`.
    pub fn sample_update_key_value(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::UpdateKeyValue(Uniform::rand(rng), rng.gen(), Uniform::rand(rng), Uniform::rand(rng))
    }

    /// Samples a random `RemoveKeyValue`.
    pub fn sample_remove_key_value(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::RemoveKeyValue(Uniform::rand(rng), rng.gen())
    }

    /// Samples a random `ReplaceMapping`.
    pub fn sample_replace_mapping(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::ReplaceMapping(Uniform::rand(rng))
    }

    /// Samples a random `RemoveMapping`.
    pub fn sample_remove_mapping(rng: &mut TestRng) -> FinalizeOperation<CurrentNetwork> {
        FinalizeOperation::RemoveMapping(Uniform::rand(rng))
    }

    /// Samples a list of random `FinalizeOperation`.
    pub fn sample_finalize_operations() -> Vec<FinalizeOperation<CurrentNetwork>> {
        let rng = &mut TestRng::default();

        vec![
            sample_initialize_mapping(rng),
            sample_insert_key_value(rng),
            sample_update_key_value(rng),
            sample_remove_key_value(rng),
            sample_replace_mapping(rng),
            sample_remove_mapping(rng),
            sample_initialize_mapping(rng),
            sample_insert_key_value(rng),
            sample_update_key_value(rng),
            sample_remove_key_value(rng),
            sample_replace_mapping(rng),
            sample_remove_mapping(rng),
        ]
    }
}
