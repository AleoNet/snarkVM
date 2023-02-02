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

mod bytes;
mod merkle;
mod serialize;
mod string;

use crate::{
    block::Transition,
    process::{Authorization, Deployment, Execution, Fee},
    program::Program,
    vm::VM,
    ConsensusStorage,
    Query,
};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{
        Ciphertext,
        Identifier,
        Plaintext,
        ProgramID,
        Record,
        TransactionLeaf,
        TransactionPath,
        TransactionTree,
        Value,
        TRANSACTION_DEPTH,
    },
    types::{Field, Group},
};

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network> {
    /// The transaction deployment publishes an Aleo program to the network.
    Deploy(N::TransactionID, Box<Deployment<N>>, Fee<N>),
    /// The transaction execution represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>, Option<Fee<N>>),
}

impl<N: Network> Transaction<N> {
    /// Initializes a new deployment transaction.
    pub fn from_deployment(deployment: Deployment<N>, fee: Fee<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");
        // Compute the transaction ID.
        let id = *Self::deployment_tree(&deployment, &fee)?.root();
        // Construct the deployment transaction.
        Ok(Self::Deploy(id.into(), Box::new(deployment), fee))
    }

    /// Initializes a new execution transaction.
    pub fn from_execution(execution: Execution<N>, additional_fee: Option<Fee<N>>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Compute the transaction ID.
        let id = *Self::execution_tree(&execution, &additional_fee)?.root();
        // Construct the execution transaction.
        Ok(Self::Execute(id.into(), execution, additional_fee))
    }
}

impl<N: Network> Transaction<N> {
    /// The maximum number of transitions allowed in a transaction.
    const MAX_TRANSITIONS: usize = usize::pow(2, TRANSACTION_DEPTH as u32);

    /// Initializes a new deployment transaction.
    pub fn deploy<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        program: &Program<N>,
        (credits, fee_in_gates): (Record<N, Plaintext<N>>, u64),
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the deployment.
        let deployment = vm.deploy(program, rng)?;
        // Compute the fee.
        let (_, fee, _) = vm.execute_fee(private_key, credits, fee_in_gates, query, rng)?;
        // Initialize the transaction.
        Self::from_deployment(deployment, fee)
    }

    /// Initializes a new execution transaction from an authorization, and an optional fee.
    pub fn execute_authorization<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        authorization: Authorization<N>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the execution.
        let (_response, execution, _metrics) = vm.execute(authorization, query, rng)?;
        // Initialize the transaction.
        Self::from_execution(execution, None)
    }

    /// Initializes a new execution transaction from an authorization, and an optional fee.
    pub fn execute_authorization_with_additional_fee<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        authorization: Authorization<N>,
        additional_fee: Option<(Record<N, Plaintext<N>>, u64)>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the execution.
        let (_response, execution, _metrics) = vm.execute(authorization, query.clone(), rng)?;
        // Compute the additional fee, if it is present.
        let additional_fee = match additional_fee {
            Some((credits, additional_fee_in_gates)) => {
                Some(vm.execute_fee(private_key, credits, additional_fee_in_gates, query, rng)?.1)
            }
            None => None,
        };
        // Initialize the transaction.
        Self::from_execution(execution, additional_fee)
    }

    /// Initializes a new execution transaction.
    #[allow(clippy::too_many_arguments)]
    pub fn execute<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        program_id: impl TryInto<ProgramID<N>>,
        function_name: impl TryInto<Identifier<N>>,
        inputs: impl ExactSizeIterator<Item = impl TryInto<Value<N>>>,
        additional_fee: Option<(Record<N, Plaintext<N>>, u64)>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the authorization.
        let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng)?;
        // Initialize the transaction.
        Self::execute_authorization_with_additional_fee(vm, private_key, authorization, additional_fee, query, rng)
    }
}

/// A helper enum for iterators and consuming iterators over a transaction.
enum IterWrap<T, I1: Iterator<Item = T>, I2: Iterator<Item = T>> {
    Deploy(I1),
    Execute(I2),
}

impl<T, I1: Iterator<Item = T>, I2: Iterator<Item = T>> Iterator for IterWrap<T, I1, I2> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Deploy(iter) => iter.next(),
            Self::Execute(iter) => iter.next(),
        }
    }
}

impl<N: Network> Transaction<N> {
    /// Returns the transaction ID.
    pub const fn id(&self) -> N::TransactionID {
        match self {
            Self::Deploy(id, ..) => *id,
            Self::Execute(id, ..) => *id,
        }
    }

    /// Returns the transaction fee, which is the sum of the transition fees.
    pub fn fee(&self) -> Result<i64> {
        // Compute the sum of the transition fees.
        self.transitions().map(Transition::fee).try_fold(0i64, |cumulative, fee| {
            cumulative.checked_add(*fee).ok_or_else(|| anyhow!("Transaction fee overflowed"))
        })
    }
}

impl<N: Network> Transaction<N> {
    /// Returns `true` if the transaction contains the given transition ID.
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        match self {
            // Check the fee.
            Self::Deploy(_, _, fee) => fee.id() == transition_id,
            // Check the execution and fee.
            Self::Execute(_, execution, fee) => {
                execution.contains_transition(transition_id)
                    || fee.as_ref().map_or(false, |fee| fee.id() == transition_id)
            }
        }
    }

    /// Returns `true` if the transaction contains the given serial number.
    pub fn contains_serial_number(&self, serial_number: &Field<N>) -> bool {
        self.transitions().any(|transition| transition.contains_serial_number(serial_number))
    }

    /// Returns `true` if the transaction contains the given commitment.
    pub fn contains_commitment(&self, commitment: &Field<N>) -> bool {
        self.transitions().any(|transition| transition.contains_commitment(commitment))
    }
}

impl<N: Network> Transaction<N> {
    /// Returns the transition with the corresponding transition ID, if it exists.
    pub fn find_transition(&self, transition_id: &N::TransitionID) -> Option<&Transition<N>> {
        match self {
            // Check the fee.
            Self::Deploy(_, _, fee) => match fee.id() == transition_id {
                true => Some(fee.transition()),
                false => None,
            },
            // Check the execution and fee.
            Self::Execute(_, execution, fee) => execution.find_transition(transition_id).or_else(|| {
                fee.as_ref().and_then(|fee| match fee.id() == transition_id {
                    true => Some(fee.transition()),
                    false => None,
                })
            }),
        }
    }

    /// Returns the transition for the given serial number, if it exists.
    pub fn find_transition_for_serial_number(&self, serial_number: &Field<N>) -> Option<&Transition<N>> {
        self.transitions().find(|transition| transition.contains_serial_number(serial_number))
    }

    /// Returns the transition for the given commitment, if it exists.
    pub fn find_transition_for_commitment(&self, commitment: &Field<N>) -> Option<&Transition<N>> {
        self.transitions().find(|transition| transition.contains_commitment(commitment))
    }

    /// Returns the record with the corresponding commitment, if it exists.
    pub fn find_record(&self, commitment: &Field<N>) -> Option<&Record<N, Ciphertext<N>>> {
        self.transitions().find_map(|transition| transition.find_record(commitment))
    }
}

impl<N: Network> Transaction<N> {
    /// Returns an iterator over the transition IDs, for all transitions.
    pub fn transition_ids(&self) -> impl '_ + Iterator<Item = &N::TransitionID> {
        self.transitions().map(Transition::id)
    }

    /// Returns an iterator over all transitions.
    pub fn transitions(&self) -> impl '_ + Iterator<Item = &Transition<N>> {
        match self {
            Self::Deploy(_, _, fee) => IterWrap::Deploy(Some(fee.transition()).into_iter()),
            Self::Execute(_, execution, additional_fee) => {
                IterWrap::Execute(execution.transitions().chain(additional_fee.as_ref().map(|f| f.transition())))
            }
        }
    }

    /* Input */

    /// Returns an iterator over the input IDs, for all transition inputs that are records.
    pub fn input_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::input_ids)
    }

    /// Returns an iterator over the serial numbers, for all transition inputs that are records.
    pub fn serial_numbers(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::serial_numbers)
    }

    /// Returns an iterator over the tags, for all transition inputs that are records.
    pub fn tags(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::tags)
    }

    /* Output */

    /// Returns an iterator over the output IDs, for all transition inputs that are records.
    pub fn output_ids(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::output_ids)
    }

    /// Returns an iterator over the commitments, for all transition outputs that are records.
    pub fn commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().flat_map(Transition::commitments)
    }

    /// Returns an iterator over the records, for all transition outputs that are records.
    pub fn records(&self) -> impl '_ + Iterator<Item = (&Field<N>, &Record<N, Ciphertext<N>>)> {
        self.transitions().flat_map(Transition::records)
    }

    /// Returns an iterator over the nonces, for all transition outputs that are records.
    pub fn nonces(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transitions().flat_map(Transition::nonces)
    }

    /// Returns an iterator over the transition public keys, for all transitions.
    pub fn transition_public_keys(&self) -> impl '_ + Iterator<Item = &Group<N>> {
        self.transitions().map(Transition::tpk)
    }

    /// Returns an iterator over the transition commitments, for all transitions.
    pub fn transition_commitments(&self) -> impl '_ + Iterator<Item = &Field<N>> {
        self.transitions().map(Transition::tcm)
    }
}

impl<N: Network> Transaction<N> {
    /// Returns a consuming iterator over the transition IDs, for all transitions.
    pub fn into_transition_ids(self) -> impl Iterator<Item = N::TransitionID> {
        self.into_transitions().map(Transition::into_id)
    }

    /// Returns a consuming iterator over all transitions.
    pub fn into_transitions(self) -> impl Iterator<Item = Transition<N>> {
        match self {
            Self::Deploy(_, _, fee) => IterWrap::Deploy(Some(fee.into_transition()).into_iter()),
            Self::Execute(_, execution, additional_fee) => {
                IterWrap::Execute(execution.into_transitions().chain(additional_fee.map(|f| f.into_transition())))
            }
        }
    }

    /// Returns a consuming iterator over the transition public keys, for all transitions.
    pub fn into_transition_public_keys(self) -> impl Iterator<Item = Group<N>> {
        self.into_transitions().map(Transition::into_tpk)
    }

    /// Returns a consuming iterator over the tags, for all transition inputs that are records.
    pub fn into_tags(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_tags)
    }

    /// Returns a consuming iterator over the serial numbers, for all transition inputs that are records.
    pub fn into_serial_numbers(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_serial_numbers)
    }

    /// Returns a consuming iterator over the commitments, for all transition outputs that are records.
    pub fn into_commitments(self) -> impl Iterator<Item = Field<N>> {
        self.into_transitions().flat_map(Transition::into_commitments)
    }

    /// Returns a consuming iterator over the records, for all transition outputs that are records.
    pub fn into_records(self) -> impl Iterator<Item = (Field<N>, Record<N, Ciphertext<N>>)> {
        self.into_transitions().flat_map(Transition::into_records)
    }

    /// Returns a consuming iterator over the nonces, for all transition outputs that are records.
    pub fn into_nonces(self) -> impl Iterator<Item = Group<N>> {
        self.into_transitions().flat_map(Transition::into_nonces)
    }
}
