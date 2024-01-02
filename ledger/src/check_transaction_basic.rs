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

impl<N: Network, C: ConsensusStorage<N>> Ledger<N, C> {
    /// Checks the given transaction is well-formed and unique.
    pub fn check_transaction_basic<R: CryptoRng + Rng>(
        &self,
        transaction: &Transaction<N>,
        rejected_id: Option<Field<N>>,
        rng: &mut R,
    ) -> Result<()> {
        // Check if the transaction exists in the cache.
        if self.verified_transactions.read().peek(&transaction.id()).is_some() {
            // If it does, perform a check without verification.
            self.vm().check_transaction(transaction, rejected_id, rng, true)
        } else {
            // Otherwise, perform the full transaction check.
            self.vm().check_transaction(transaction, rejected_id, rng, false)?;

            // If the check passes and it's not a fee transaction,
            // save its ID to the cache.
            if !matches!(transaction, Transaction::Fee(..)) {
                self.verified_transactions.write().push(transaction.id(), ());
            }

            Ok(())
        }
    }
}
