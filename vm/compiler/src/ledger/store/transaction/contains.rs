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

use super::*;

impl<
    N: Network,
    DeploymentsMap: for<'a> Map<'a, N::TransactionID, (Deployment<N>, N::TransitionID)>,
    ExecutionsMap: for<'a> Map<'a, N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>,
    TransitionPublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
    SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>,
    OriginsMap: for<'a> Map<'a, Origin<N>, N::TransitionID>,
    NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>,
>
    TransactionStore<
        N,
        DeploymentsMap,
        ExecutionsMap,
        TransitionsMap,
        TransitionPublicKeysMap,
        SerialNumbersMap,
        CommitmentsMap,
        OriginsMap,
        NonceMap,
    >
{
    /// Returns `true` if the given transaction exists.
    pub fn contains_transaction(&self, transaction: &Transaction<N>) -> Result<bool> {
        self.contains_transaction_id(&transaction.id())
    }

    /// Returns `true` if the given transaction ID exists.
    pub fn contains_transaction_id(&self, transaction_id: &N::TransactionID) -> Result<bool> {
        self.deployments.contains_key(transaction_id).or_else(|_| self.executions.contains_key(transaction_id))
    }

    /// Returns `true` if the given transition exists.
    pub fn contains_transition(&self, transition: &Transition<N>) -> Result<bool> {
        self.contains_transition_id(transition.id())
    }

    /// Returns `true` if the given transition ID exists.
    pub fn contains_transition_id(&self, transition_id: &N::TransitionID) -> Result<bool> {
        self.transitions.contains_key(transition_id)
    }

    /// Returns `true` if the given transition public key exists.
    pub fn contains_transition_public_key(&self, tpk: &Group<N>) -> Result<bool> {
        self.transition_public_keys.contains_key(tpk)
    }

    /// Returns `true` if the given origin exists.
    pub fn contains_origin(&self, origin: &Origin<N>) -> Result<bool> {
        self.origins.contains_key(origin)
    }

    // /// Returns `true` if the given tag exists.
    // pub fn contains_tag(&self, tag: &Field<N>) -> Result<bool> {
    //     self.tags.contains_key(tag)
    // }

    /// Returns `true` if the given serial number exists.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> Result<bool> {
        self.serial_numbers.contains_key(serial_number)
    }

    /// Returns `true` if the given commitment exists.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> Result<bool> {
        self.commitments.contains_key(commitment)
    }

    /// Returns `true` if the given nonce exists.
    pub fn contains_nonce(&self, nonce: &Group<N>) -> Result<bool> {
        self.nonces.contains_key(nonce)
    }
}
