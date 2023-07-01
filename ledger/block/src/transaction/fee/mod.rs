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

mod bytes;
mod serialize;
mod string;

use crate::{Input, Transition};
use console::{
    network::prelude::*,
    program::{Literal, Plaintext},
    types::U64,
};
use synthesizer_snark::Proof;

#[derive(Clone, PartialEq, Eq)]
pub struct Fee<N: Network> {
    /// The transition.
    transition: Transition<N>,
    /// The global state root.
    global_state_root: N::StateRoot,
    /// The proof.
    proof: Option<Proof<N>>,
}

impl<N: Network> Fee<N> {
    /// Initializes a new `Fee` instance with the given transition, global state root, and proof.
    pub fn from(transition: Transition<N>, global_state_root: N::StateRoot, proof: Option<Proof<N>>) -> Self {
        // Return the new `Fee` instance.
        Self { transition, global_state_root, proof }
    }

    /// Returns 'true' if the fee amount is zero.
    pub fn is_zero(&self) -> Result<bool> {
        self.amount().map(|amount| amount.is_zero())
    }

    /// Returns the amount (in microcredits).
    pub fn amount(&self) -> Result<U64<N>> {
        // Retrieve the amount (in microcredits) as a plaintext value.
        match self.transition.inputs().get(1) {
            Some(Input::Public(_, Some(Plaintext::Literal(Literal::U64(microcredits), _)))) => Ok(*microcredits),
            _ => bail!("Failed to retrieve the fee (in microcredits) from the fee transition"),
        }
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> &N::TransitionID {
        self.transition.id()
    }

    /// Returns the transition.
    pub const fn transition(&self) -> &Transition<N> {
        &self.transition
    }

    /// Returns the transition, consuming self in the process.
    pub fn into_transition(self) -> Transition<N> {
        self.transition
    }

    /// Returns the global state root.
    pub const fn global_state_root(&self) -> N::StateRoot {
        self.global_state_root
    }

    /// Returns the proof.
    pub const fn proof(&self) -> Option<&Proof<N>> {
        self.proof.as_ref()
    }
}

impl<N: Network> Deref for Fee<N> {
    type Target = Transition<N>;

    fn deref(&self) -> &Self::Target {
        &self.transition
    }
}

#[cfg(any(test, feature = "test"))]
pub mod test_helpers {
    use super::*;
    use crate::Transaction;

    type CurrentNetwork = console::network::Testnet3;

    /// Samples a random fee.
    pub(crate) fn sample_fee(rng: &mut TestRng) -> Fee<CurrentNetwork> {
        if let Transaction::Execute(_, _, fee) =
            crate::transaction::test_helpers::sample_execution_transaction_with_fee(rng)
        {
            fee.unwrap()
        } else {
            unreachable!()
        }
    }
}
