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
    use console::types::Field;
    use ledger_query::Query;
    use ledger_store::{helpers::memory::BlockMemory, BlockStore};
    use synthesizer_process::Process;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = console::network::Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    /// Samples a random hardcoded fee.
    pub fn sample_fee_hardcoded(rng: &mut TestRng) -> Fee<CurrentNetwork> {
        static INSTANCE: OnceCell<Fee<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Sample a deployment or execution ID.
                let deployment_or_execution_id = Field::rand(rng);
                // Sample a fee.
                sample_fee(deployment_or_execution_id, rng)
            })
            .clone()
    }

    /// Samples a random fee.
    pub fn sample_fee(deployment_or_execution_id: Field<CurrentNetwork>, rng: &mut TestRng) -> Fee<CurrentNetwork> {
        // Sample the genesis block, transaction, and private key.
        let (block, transaction, private_key) = crate::test_helpers::sample_genesis_block_and_components(rng);
        // Retrieve a credits record.
        let credits = transaction.records().next().unwrap().1.clone();
        // Decrypt the record.
        let credits = credits.decrypt(&private_key.try_into().unwrap()).unwrap();
        // Set the fee amount.
        let fee = 10_000_000;

        // Initialize the process.
        let process = Process::load().unwrap();
        // Compute the fee trace.
        let (_, _, mut trace) =
            process.execute_fee::<CurrentAleo, _>(&private_key, credits, fee, deployment_or_execution_id, rng).unwrap();

        // Initialize a new block store.
        let block_store = BlockStore::<CurrentNetwork, BlockMemory<_>>::open(None).unwrap();
        // Insert the block into the block store.
        // Note: This is a testing-only hack to adhere to Rust's dependency cycle rules.
        block_store.insert(&FromStr::from_str(&block.to_string()).unwrap()).unwrap();

        // Prepare the assignments.
        trace.prepare(Query::from(block_store)).unwrap();
        // Compute the proof and construct the fee.
        let fee = trace.prove_fee::<CurrentAleo, _>(rng).unwrap();

        // Convert the fee.
        // Note: This is a testing-only hack to adhere to Rust's dependency cycle rules.
        let fee = Fee::from_str(&fee.to_string()).unwrap();
        // Return the fee.
        fee
    }
}
