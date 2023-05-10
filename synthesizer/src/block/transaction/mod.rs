// Copyright (C) 2019-2023 Aleo Systems Inc.
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
        ProgramOwner,
        Record,
        TransactionLeaf,
        TransactionPath,
        TransactionTree,
        Value,
        TRANSACTION_DEPTH,
    },
    types::{Field, Group, U64},
};

#[derive(Clone, PartialEq, Eq)]
pub enum Transaction<N: Network> {
    /// The deploy transaction publishes an Aleo program to the network.
    Deploy(N::TransactionID, ProgramOwner<N>, Box<Deployment<N>>, Fee<N>),
    /// The execute transaction represents a call to an Aleo program.
    Execute(N::TransactionID, Execution<N>, Option<Fee<N>>),
    /// The fee transaction represents a fee paid to the network, used for rejected transactions.
    Fee(N::TransactionID, Fee<N>),
}

impl<N: Network> Transaction<N> {
    /// Initializes a new deployment transaction.
    pub fn from_deployment(owner: ProgramOwner<N>, deployment: Deployment<N>, fee: Fee<N>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");
        // Compute the transaction ID.
        let id = *Self::deployment_tree(&deployment, &fee)?.root();
        // Ensure the owner signed the correct transaction ID.
        ensure!(owner.verify(id.into()), "Attempted to create a transaction deployment with an invalid owner");
        // Construct the deployment transaction.
        Ok(Self::Deploy(id.into(), owner, Box::new(deployment), fee))
    }

    /// Initializes a new execution transaction.
    pub fn from_execution(execution: Execution<N>, fee: Option<Fee<N>>) -> Result<Self> {
        // Ensure the transaction is not empty.
        ensure!(!execution.is_empty(), "Attempted to create an empty transaction execution");
        // Compute the transaction ID.
        let id = *Self::execution_tree(&execution, &fee)?.root();
        // Construct the execution transaction.
        Ok(Self::Execute(id.into(), execution, fee))
    }

    /// Initializes a new fee transaction.
    pub fn from_fee(fee: Fee<N>) -> Result<Self> {
        // Ensure the fee is nonzero.
        ensure!(!fee.is_zero()?, "Attempted to create a zero fee transaction");
        // Compute the transaction ID.
        let id = *Self::fee_tree(&fee)?.root();
        // Construct the execution transaction.
        Ok(Self::Fee(id.into(), fee))
    }
}

impl<N: Network> Transaction<N> {
    /// The maximum number of transitions allowed in a transaction.
    const MAX_TRANSITIONS: usize = usize::pow(2, TRANSACTION_DEPTH as u32);

    /// Initializes a new deployment transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the deployment fee.
    pub fn deploy<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        program: &Program<N>,
        (fee_record, priority_fee_in_microcredits): (Record<N, Plaintext<N>>, u64),
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the deployment.
        let deployment = vm.deploy(program, rng)?;
        // Ensure the transaction is not empty.
        ensure!(!deployment.program().functions().is_empty(), "Attempted to create an empty transaction deployment");

        // Determine the fee.
        let fee_in_microcredits = deployment
            .size_in_bytes()?
            .checked_mul(N::DEPLOYMENT_FEE_MULTIPLIER)
            .and_then(|deployment_fee| deployment_fee.checked_add(priority_fee_in_microcredits))
            .ok_or_else(|| anyhow!("Fee overflowed for a deployment transaction"))?;

        // Compute the fee.
        let (_, fee, _) = vm.execute_fee(private_key, fee_record, fee_in_microcredits, query, rng)?;

        // Construct the owner.
        let id = *Self::deployment_tree(&deployment, &fee)?.root();
        let owner = ProgramOwner::new(private_key, id.into(), rng)?;

        // Initialize the transaction.
        Self::from_deployment(owner, deployment, fee)
    }

    /// Initializes a new execution transaction.
    ///
    /// The `priority_fee_in_microcredits` is an additional fee **on top** of the deployment fee.
    pub fn execute<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        (program_id, function_name): (impl TryInto<ProgramID<N>>, impl TryInto<Identifier<N>>),
        inputs: impl ExactSizeIterator<Item = impl TryInto<Value<N>>>,
        fee: Option<(Record<N, Plaintext<N>>, u64)>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the authorization.
        let authorization = vm.authorize(private_key, program_id, function_name, inputs, rng)?;
        // Compute the execution.
        let (_response, execution, _metrics) = vm.execute(authorization, query.clone(), rng)?;
        // Compute the fee.
        let fee = match fee {
            None => None,
            Some((credits, priority_fee_in_microcredits)) => {
                // Determine the fee.
                let fee_in_microcredits = execution
                    .size_in_bytes()?
                    .checked_add(priority_fee_in_microcredits)
                    .ok_or_else(|| anyhow!("Fee overflowed for an execution transaction"))?;
                // Compute the fee.
                Some(vm.execute_fee(private_key, credits, fee_in_microcredits, query, rng)?.1)
            }
        };
        // Initialize the transaction.
        Self::from_execution(execution, fee)
    }

    /// Initializes a new fee.
    pub fn execute_fee<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Fee<N>> {
        Ok(vm.execute_fee(private_key, credits, fee_in_microcredits, query, rng)?.1)
    }

    /// Initializes a new execution transaction from an authorization.
    pub fn execute_authorization<C: ConsensusStorage<N>, R: Rng + CryptoRng>(
        vm: &VM<N, C>,
        authorization: Authorization<N>,
        fee: Option<Fee<N>>,
        query: Option<Query<N, C::BlockStorage>>,
        rng: &mut R,
    ) -> Result<Self> {
        // Compute the execution.
        let (_response, execution, _metrics) = vm.execute(authorization, query, rng)?;
        // Initialize the transaction.
        Self::from_execution(execution, fee)
    }
}

impl<N: Network> Transaction<N> {
    /// Returns `true` if the transaction is a deploy transaction.
    #[inline]
    pub fn is_deploy(&self) -> bool {
        matches!(self, Self::Deploy(..))
    }

    /// Returns `true` if the transaction is an execute transaction.
    #[inline]
    pub fn is_execute(&self) -> bool {
        matches!(self, Self::Execute(..))
    }

    /// Returns `true` if the transaction is a fee transaction.
    #[inline]
    pub fn is_fee(&self) -> bool {
        matches!(self, Self::Fee(..))
    }

    /// Returns `true` if this is a coinbase transaction.
    #[inline]
    pub fn is_coinbase(&self) -> bool {
        // Case 1 - The transaction contains 1 transition, which calls 'credits.aleo/mint'.
        if let Self::Execute(_, execution, _) = self {
            // Ensure there is 1 transition.
            if execution.len() == 1 {
                // Retrieve the transition.
                if let Ok(transition) = execution.get(0) {
                    // Check if it calls 'credits.aleo/mint'.
                    if transition.program_id().to_string() == "credits.aleo"
                        && transition.function_name().to_string() == "mint"
                    {
                        return true;
                    }
                }
            }
        }
        // Otherwise, return 'false'.
        false
    }

    /// Returns `true` if this is a `split` transaction.
    #[inline]
    pub fn is_split(&self) -> bool {
        // Case 1 - The transaction contains 1 transition, which calls 'credits.aleo/split'.
        if let Self::Execute(_, execution, _) = self {
            // Ensure there is 1 transition.
            if execution.len() == 1 {
                // Retrieve the transition.
                if let Ok(transition) = execution.get(0) {
                    // Check if it calls 'credits.aleo/split'.
                    if transition.program_id().to_string() == "credits.aleo"
                        && transition.function_name().to_string() == "split"
                    {
                        return true;
                    }
                }
            }
        }
        // Otherwise, return 'false'.
        false
    }
}

/// A helper enum for iterators and consuming iterators over a transaction.
enum IterWrap<T, I1: Iterator<Item = T>, I2: Iterator<Item = T>, I3: Iterator<Item = T>> {
    Deploy(I1),
    Execute(I2),
    Fee(I3),
}

impl<T, I1: Iterator<Item = T>, I2: Iterator<Item = T>, I3: Iterator<Item = T>> Iterator for IterWrap<T, I1, I2, I3> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Deploy(iter) => iter.next(),
            Self::Execute(iter) => iter.next(),
            Self::Fee(iter) => iter.next(),
        }
    }
}

impl<N: Network> Transaction<N> {
    /// Returns the transaction ID.
    pub const fn id(&self) -> N::TransactionID {
        match self {
            Self::Deploy(id, ..) => *id,
            Self::Execute(id, ..) => *id,
            Self::Fee(id, ..) => *id,
        }
    }

    /// Returns the transaction fee.
    pub fn fee(&self) -> Result<U64<N>> {
        match self {
            Self::Deploy(_, _, _, fee) => fee.amount(),
            Self::Execute(_, _, Some(fee)) => fee.amount(),
            Self::Execute(_, _, None) => Ok(U64::zero()),
            Self::Fee(_, fee) => fee.amount(),
        }
    }

    /// Returns the fee transition.
    pub fn fee_transition(&self) -> Option<Fee<N>> {
        match self {
            Self::Deploy(_, _, _, fee) => Some(fee.clone()),
            Self::Execute(_, _, fee) => fee.clone(),
            Self::Fee(_, fee) => Some(fee.clone()),
        }
    }
}

impl<N: Network> Transaction<N> {
    /// Returns `true` if the transaction contains the given transition ID.
    pub fn contains_transition(&self, transition_id: &N::TransitionID) -> bool {
        match self {
            // Check the fee.
            Self::Deploy(_, _, _, fee) => fee.id() == transition_id,
            // Check the execution and fee.
            Self::Execute(_, execution, fee) => {
                execution.contains_transition(transition_id)
                    || fee.as_ref().map_or(false, |fee| fee.id() == transition_id)
            }
            // Check the fee.
            Self::Fee(_, fee) => fee.id() == transition_id,
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
            Self::Deploy(_, _, _, fee) => match fee.id() == transition_id {
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
            // Check the fee.
            Self::Fee(_, fee) => match fee.id() == transition_id {
                true => Some(fee.transition()),
                false => None,
            },
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
            Self::Deploy(_, _, _, fee) => IterWrap::Deploy(Some(fee.transition()).into_iter()),
            Self::Execute(_, execution, fee) => {
                IterWrap::Execute(execution.transitions().chain(fee.as_ref().map(|fee| fee.transition())))
            }
            Self::Fee(_, fee) => IterWrap::Fee(Some(fee.transition()).into_iter()),
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
            Self::Deploy(_, _, _, fee) => IterWrap::Deploy(Some(fee.into_transition()).into_iter()),
            Self::Execute(_, execution, fee) => {
                IterWrap::Execute(execution.into_transitions().chain(fee.map(|fee| fee.into_transition())))
            }
            Self::Fee(_, fee) => IterWrap::Fee(Some(fee.into_transition()).into_iter()),
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
