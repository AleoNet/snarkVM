// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use snarkvm_circuits::{Aleo, Boolean, Field, Scalar};

pub trait AleoDPC: Aleo {
    /// Returns the BHP hash for a block hash.
    fn hash_block_hash_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a block header - leaf.
    fn hash_block_header_leaf_ped(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen hash for a block header - two to one.
    fn hash_block_header_two_to_one_ped(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen commitment for record commitments.
    fn hash_record_commitment_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Poseidon hash for function ids.
    fn hash_function_id_psd(input: &[Field<Self>]) -> Field<Self>;

    /// Returns the Poseidon hash for function inputs.
    fn hash_function_input_psd(input: &[Field<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the ledger root - leaf.
    fn hash_ledger_root_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the ledger root - two to one
    fn hash_ledger_root_two_to_one_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Poseidon PRF for the serial number.
    fn prf_serial_number_psd(seed: &Field<Self>, input: &[Field<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transactions root - leaf.
    fn hash_transactions_root_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transactions root - two to one.
    fn hash_transactions_root_two_to_one_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transaction ids - leaf.
    fn hash_transaction_id_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transaction ids - two to one.
    fn hash_transaction_id_two_to_one_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transaction ids - leaf.
    fn hash_transaction_id_bhp_ped(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transaction ids - two to one.
    fn hash_transaction_id_two_to_one_bhp_ped(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transition ids - leaf.
    fn hash_transition_id_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the BHP hash for the transition ids - two to one.
    fn hash_transition_id_two_to_one_bhp(input: &[Boolean<Self>]) -> Field<Self>;

    /// Returns the Pedersen commitment for the value commitment.
    fn commit_value_ped(input: &[Boolean<Self>], randomizer: &Scalar<Self>) -> Field<Self>;
}
