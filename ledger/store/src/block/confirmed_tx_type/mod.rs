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

mod bytes;
mod serialize;
mod string;

use super::*;

#[derive(Clone, PartialEq, Eq)]
pub enum ConfirmedTxType<N: Network> {
    /// A deploy transaction that was accepted.
    AcceptedDeploy(u32),
    /// An execute transaction that was accepted.
    AcceptedExecute(u32),
    /// A deploy transaction that was rejected.
    RejectedDeploy(u32, Rejected<N>),
    /// An execute transaction that was rejected.
    RejectedExecute(u32, Rejected<N>),
}

#[cfg(test)]
pub mod test_helpers {
    use super::*;
    use console::network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    /// Samples an accepted deploy.
    pub(crate) fn sample_accepted_deploy(rng: &mut TestRng) -> ConfirmedTxType<CurrentNetwork> {
        // Return the accepted deploy.
        ConfirmedTxType::AcceptedDeploy(rng.gen())
    }

    /// Samples an accepted execution.
    pub(crate) fn sample_accepted_execution(rng: &mut TestRng) -> ConfirmedTxType<CurrentNetwork> {
        // Return the accepted execution.
        ConfirmedTxType::AcceptedExecute(rng.gen())
    }

    /// Samples a rejected deploy.
    pub(crate) fn sample_rejected_deploy(rng: &mut TestRng) -> ConfirmedTxType<CurrentNetwork> {
        // Sample the rejected deployment.
        let rejected = ledger_test_helpers::sample_rejected_deployment(rng.gen(), rng);
        // Return the rejected deploy.
        ConfirmedTxType::RejectedDeploy(rng.gen(), rejected)
    }

    /// Samples a rejected execution.
    pub(crate) fn sample_rejected_execute(rng: &mut TestRng) -> ConfirmedTxType<CurrentNetwork> {
        // Sample the rejected execution.
        let rejected = ledger_test_helpers::sample_rejected_execution(rng.gen(), rng);
        // Return the rejected execution.
        ConfirmedTxType::RejectedExecute(rng.gen(), rejected)
    }

    /// Sample a list of randomly rejected transactions.
    pub(crate) fn sample_confirmed_tx_types() -> Vec<ConfirmedTxType<CurrentNetwork>> {
        let rng = &mut TestRng::default();

        vec![
            sample_accepted_deploy(rng),
            sample_accepted_execution(rng),
            sample_rejected_deploy(rng),
            sample_rejected_execute(rng),
        ]
    }
}
