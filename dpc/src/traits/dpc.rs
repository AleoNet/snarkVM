// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{
    traits::{AccountScheme, Parameters, RecordCommitmentTree, RecordSerialNumberTree, TransactionScheme},
    Executable,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait DPCScheme<C: Parameters>: Sized {
    type Account: AccountScheme;
    type Authorization;
    type Execution;
    type StateTransition;
    type Transaction: TransactionScheme;

    /// Initializes a saved instance of DPC.
    fn load() -> Self;

    /// Returns an authorization to execute a state transition.
    fn authorize<R: Rng + CryptoRng>(
        private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        state: &Self::StateTransition,
        rng: &mut R,
    ) -> Result<Self::Authorization>;

    /// Returns a transaction by executing an authorized state transition.
    fn execute<L: RecordCommitmentTree<C>, R: Rng + CryptoRng>(
        compute_keys: &Vec<<Self::Account as AccountScheme>::ComputeKey>,
        authorization: Self::Authorization,
        executables: &Vec<Executable<C>>,
        ledger: &L,
        rng: &mut R,
    ) -> Result<Self::Transaction>;

    /// Returns true iff the transaction is valid according to the ledger.
    fn verify<L: RecordCommitmentTree<C> + RecordSerialNumberTree<C>>(
        transaction: &Self::Transaction,
        ledger: &L,
    ) -> bool;

    /// Returns true iff all the transactions in the block are valid according to the ledger.
    fn verify_transactions<L: RecordCommitmentTree<C> + RecordSerialNumberTree<C> + Sync>(
        block: &[Self::Transaction],
        ledger: &L,
    ) -> bool;
}
