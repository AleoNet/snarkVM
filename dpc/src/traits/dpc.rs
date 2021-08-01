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

use crate::traits::{
    AccountScheme,
    Parameters,
    RecordCommitmentTree,
    RecordScheme,
    RecordSerialNumberTree,
    TransactionScheme,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait DPCScheme<C: Parameters>: Sized {
    type Account: AccountScheme;
    type Authorization;
    type Execution;
    type Record: RecordScheme<Owner = <Self::Account as AccountScheme>::Address>;
    type Transaction: TransactionScheme<SerialNumber = <Self::Record as RecordScheme>::SerialNumber>;

    /// Initializes a new instance of DPC.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self>;

    /// Loads the saved instance of DPC.
    fn load(verify_only: bool) -> Result<Self>;

    /// Returns an authorized transaction kernel for use to craft an Aleo transaction.
    #[allow(clippy::too_many_arguments)]
    fn authorize<R: Rng + CryptoRng>(
        &self,
        old_private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        old_records: Vec<Self::Record>,
        new_records: Vec<Self::Record>,
        memo: <Self::Transaction as TransactionScheme>::Memo,
        rng: &mut R,
    ) -> Result<Self::Authorization>;

    /// Returns a transaction based on the authorized transaction kernel.
    fn execute<L: RecordCommitmentTree<C>, R: Rng + CryptoRng>(
        &self,
        old_private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        transaction_kernel: Self::Authorization,
        program_proofs: Vec<Self::Execution>,
        ledger: &L,
        rng: &mut R,
    ) -> Result<Self::Transaction>;

    /// Returns true iff the transaction is valid according to the ledger.
    fn verify<L: RecordCommitmentTree<C> + RecordSerialNumberTree<C>>(
        &self,
        transaction: &Self::Transaction,
        ledger: &L,
    ) -> bool;

    /// Returns true iff all the transactions in the block are valid according to the ledger.
    fn verify_transactions<L: RecordCommitmentTree<C> + RecordSerialNumberTree<C>>(
        &self,
        block: &[Self::Transaction],
        ledger: &L,
    ) -> bool;
}
