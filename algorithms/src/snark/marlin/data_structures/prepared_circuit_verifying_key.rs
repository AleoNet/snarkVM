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

use crate::snark::marlin::{CircuitVerifyingKey, MarlinMode};
use snarkvm_curves::PairingEngine;
use std::cmp::Ordering;
/// Verification key, prepared (preprocessed) for use in pairings.

#[derive(Clone)]
pub struct PreparedCircuitVerifyingKey<E: PairingEngine, MM: MarlinMode> {
    /// Size of the variable domain.
    pub constraint_domain_size: u64,
    /// Size of the domain that represents A.
    pub non_zero_a_domain_size: u64,
    /// Size of the domain that represents B.
    pub non_zero_b_domain_size: u64,
    /// Size of the domain that represents C.
    pub non_zero_c_domain_size: u64,
    /// Non-prepared verification key, for use in native "prepared verify" (which
    /// is actually standard verify), as well as in absorbing the original vk into
    /// the Fiat-Shamir sponge.
    pub orig_vk: CircuitVerifyingKey<E, MM>,
}

impl<E: PairingEngine, MM: MarlinMode> Ord for PreparedCircuitVerifyingKey<E, MM> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.orig_vk.id.cmp(&other.orig_vk.id)
    }
}

impl<E: PairingEngine, MM: MarlinMode> PartialOrd for PreparedCircuitVerifyingKey<E, MM> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: PairingEngine, MM: MarlinMode> PartialEq for PreparedCircuitVerifyingKey<E, MM> {
    fn eq(&self, other: &Self) -> bool {
        self.orig_vk.id == other.orig_vk.id
    }
}

impl<E: PairingEngine, MM: MarlinMode> Eq for PreparedCircuitVerifyingKey<E, MM> {}
