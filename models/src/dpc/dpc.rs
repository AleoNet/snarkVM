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
    dpc::Record,
    objects::{AccountScheme, LedgerScheme, Transaction},
};

use rand::Rng;

pub trait DPCScheme<L: LedgerScheme> {
    type Account: AccountScheme;
    type Payload;
    type NetworkParameters;
    type PrivateProgramInput;
    type Record: Record<Owner = <Self::Account as AccountScheme>::AccountAddress>;
    type SystemParameters;
    type Transaction: Transaction<SerialNumber = <Self::Record as Record>::SerialNumber>;
    type LocalData;
    type TransactionKernel;

    /// Returns public parameters for the DPC.
    fn setup<R: Rng>(ledger_parameters: &L::MerkleParameters, rng: &mut R) -> anyhow::Result<Self::NetworkParameters>;

    /// Returns an account, given the system parameters, metadata, and an RNG.
    fn create_account<R: Rng>(parameters: &Self::SystemParameters, rng: &mut R) -> anyhow::Result<Self::Account>;

    /// Returns the execution context required for program snark and DPC transaction generation.
    #[allow(clippy::too_many_arguments)]
    fn execute_offline<R: Rng>(
        parameters: Self::SystemParameters,
        old_records: Vec<Self::Record>,
        old_account_private_keys: Vec<<Self::Account as AccountScheme>::AccountPrivateKey>,
        new_record_owners: Vec<<Self::Account as AccountScheme>::AccountAddress>,
        new_is_dummy_flags: &[bool],
        new_values: &[u64],
        new_payloads: Vec<Self::Payload>,
        new_birth_program_ids: Vec<Vec<u8>>,
        new_death_program_ids: Vec<Vec<u8>>,
        memorandum: <Self::Transaction as Transaction>::Memorandum,
        network_id: u8,
        rng: &mut R,
    ) -> anyhow::Result<Self::TransactionKernel>;

    /// Returns new records and a transaction based on the authorized
    /// consumption of old records.
    fn execute_online<R: Rng>(
        parameters: &Self::NetworkParameters,
        transaction_kernel: Self::TransactionKernel,
        old_death_program_proofs: Vec<Self::PrivateProgramInput>,
        new_birth_program_proofs: Vec<Self::PrivateProgramInput>,
        ledger: &L,
        rng: &mut R,
    ) -> anyhow::Result<(Vec<Self::Record>, Self::Transaction)>;

    /// Returns true iff the transaction is valid according to the ledger.
    fn verify(
        parameters: &Self::NetworkParameters,
        transaction: &Self::Transaction,
        ledger: &L,
    ) -> anyhow::Result<bool>;

    /// Returns true iff all the transactions in the block are valid according to the ledger.
    fn verify_transactions(
        parameters: &Self::NetworkParameters,
        block: &[Self::Transaction],
        ledger: &L,
    ) -> anyhow::Result<bool>;
}
