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

use crate::{
    cow_to_cloned,
    cow_to_copied,
    ledger::{
        map::{memory_map::MemoryMap, Map, MapRead},
        store::{CowIter, TransitionMemory, TransitionStorage, TransitionStore},
        transaction::{AdditionalFee, Transaction},
    },
    process::Deployment,
    program::Program,
    snark::{Certificate, VerifyingKey},
};
use console::{
    network::prelude::*,
    program::{Identifier, ProgramID},
    types::Field,
};

use anyhow::Result;
use indexmap::IndexMap;
use std::borrow::Cow;

/// A trait for deployment storage.
pub trait DeploymentStorage<N: Network>: Clone {
    /// The mapping of `transaction ID` to `program ID`.
    type IDMap: for<'a> Map<'a, N::TransactionID, ProgramID<N>>;
    /// The mapping of `program ID` to `transaction ID`.
    type ReverseIDMap: for<'a> Map<'a, ProgramID<N>, N::TransactionID>;
    /// The mapping of `program ID` to `edition`.
    type EditionMap: for<'a> Map<'a, ProgramID<N>, u16>;
    /// The mapping of `program ID` to `program`.
    type ProgramMap: for<'a> Map<'a, ProgramID<N>, Program<N>>;
    /// The mapping of `(program ID, function name)` to `verifying key`.
    type VerifyingKeyMap: for<'a> Map<'a, (ProgramID<N>, Identifier<N>), VerifyingKey<N>>;
    /// The mapping of `(program ID, function name)` to `certificate`.
    type CertificateMap: for<'a> Map<'a, (ProgramID<N>, Identifier<N>), Certificate<N>>;
    /// The mapping of `transaction ID` to `additional fee ID`.
    type AdditionalFeeMap: for<'a> Map<'a, N::TransactionID, N::TransitionID>;
    /// The transition storage.
    type TransitionStorage: TransitionStorage<N>;

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap;
    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap;
    /// Returns the edition map.
    fn edition_map(&self) -> &Self::EditionMap;
    /// Returns the program map.
    fn program_map(&self) -> &Self::ProgramMap;
    /// Returns the verifying key map.
    fn verifying_key_map(&self) -> &Self::VerifyingKeyMap;
    /// Returns the certificate map.
    fn certificate_map(&self) -> &Self::CertificateMap;
    /// Returns the additional fee map.
    fn additional_fee_map(&self) -> &Self::AdditionalFeeMap;
    /// Returns the transition storage.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage>;

    /// Returns the transaction ID that contains the given `program ID`.
    fn find_transaction_id(&self, program_id: &ProgramID<N>) -> Result<Option<N::TransactionID>> {
        match self.reverse_id_map().get(program_id)? {
            Some(transaction_id) => Ok(Some(cow_to_copied!(transaction_id))),
            None => Ok(None),
        }
    }

    /// Returns the program ID for the given `transaction ID`.
    fn get_program_id(&self, transaction_id: &N::TransactionID) -> Result<ProgramID<N>> {
        // Retrieve the program ID.
        match self.id_map().get(transaction_id)? {
            Some(program_id) => Ok(cow_to_copied!(program_id)),
            None => bail!("Failed to locate transaction '{transaction_id}'"),
        }
    }

    /// Returns the program for the given `program ID`.
    fn get_program(&self, program_id: &ProgramID<N>) -> Result<Program<N>> {
        match self.program_map().get(program_id)? {
            Some(program) => Ok(cow_to_cloned!(program)),
            None => bail!("Program '{program_id}' was not found in storage"),
        }
    }

    /// Returns the edition for the given `program ID`.
    fn get_edition(&self, program_id: &ProgramID<N>) -> Result<u16> {
        match self.edition_map().get(program_id)? {
            Some(edition) => Ok(cow_to_copied!(edition)),
            None => bail!("Failed to locate the edition for program '{program_id}'"),
        }
    }

    /// Returns the verifying key for the given `program ID` and `function name`.
    fn get_verifying_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> Result<VerifyingKey<N>> {
        match self.verifying_key_map().get(&(*program_id, *function_name))? {
            Some(verifying_key) => Ok(cow_to_cloned!(verifying_key)),
            None => bail!("Failed to locate the verifying key for '{program_id}/{function_name}'"),
        }
    }

    /// Returns the certificate for the given `program ID` and `function name`.
    fn get_certificate(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> Result<Certificate<N>> {
        match self.certificate_map().get(&(*program_id, *function_name))? {
            Some(certificate) => Ok(cow_to_cloned!(certificate)),
            None => bail!("Failed to locate the certificate for '{program_id}/{function_name}'"),
        }
    }

    /// Returns the deployment for the given `transaction ID`.
    fn get_deployment(&self, transaction_id: &N::TransactionID) -> Result<Deployment<N>> {
        // Retrieve the program ID.
        let program_id = self.get_program_id(transaction_id)?;
        // Retrieve the program.
        let program = self.get_program(&program_id)?;
        // Retrieve the edition.
        let edition = self.get_edition(&program_id)?;

        // Initialize a vector for the verifying keys and certificates.
        let mut verifying_keys = IndexMap::new();

        // Retrieve the verifying keys and certificates.
        for function_name in program.functions().keys() {
            // Retrieve the verifying key.
            let verifying_key = self.get_verifying_key(&program_id, function_name)?;
            // Retrieve the certificate.
            let certificate = self.get_certificate(&program_id, function_name)?;
            // Add the verifying key and certificate to the deployment.
            verifying_keys.insert(*function_name, (verifying_key, certificate));
        }

        // Return the deployment.
        Deployment::new(edition, program, verifying_keys)
    }

    /// Returns the additional fee for the given `transaction ID`.
    fn get_additional_fee(&self, transaction_id: &N::TransactionID) -> Result<AdditionalFee<N>> {
        // Retrieve the additional fee ID.
        let additional_fee_id = match self.additional_fee_map().get(transaction_id)? {
            Some(additional_fee_id) => cow_to_copied!(additional_fee_id),
            None => bail!("Failed to locate the additional fee ID for transaction '{transaction_id}'"),
        };
        // Retrieve the additional fee transition.
        match self.transition_store().get_transition(&additional_fee_id)? {
            Some(transition) => Ok(transition),
            None => bail!("Failed to locate the additional fee transition for transaction '{transaction_id}'"),
        }
    }

    /// Returns the transaction for the given `transaction ID`.
    fn get_transaction(&self, transaction_id: &N::TransactionID) -> Result<Transaction<N>> {
        // Retrieve the deployment.
        let deployment = self.get_deployment(transaction_id)?;
        // Retrieve the additional fee.
        let additional_fee = self.get_additional_fee(transaction_id)?;

        // Construct the deployment transaction.
        let deployment_transaction = Transaction::from_deployment(deployment, additional_fee)?;
        // Ensure the transaction ID matches.
        match *transaction_id == deployment_transaction.id() {
            true => Ok(deployment_transaction),
            false => bail!("The deployment transaction ID does not match '{transaction_id}'"),
        }
    }

    /// Stores the given `deployment transaction` pair into storage.
    fn insert(&self, transaction: &Transaction<N>) -> Result<()> {
        // Ensure the transaction is a deployment.
        let (transaction_id, deployment, additional_fee) = match transaction {
            Transaction::Deploy(transaction_id, deployment, additional_fee) => {
                (transaction_id, deployment, additional_fee)
            }
            Transaction::Execute(..) => {
                bail!("Attempted to insert non-deployment transaction into deployment storage.")
            }
        };

        // Retrieve the program.
        let program = deployment.program();
        // Retrieve the program ID.
        let program_id = *program.id();

        // Ensure the number of functions matches the number of verifying keys.
        if program.functions().len() != deployment.verifying_keys().len() {
            bail!("Deployment has an incorrect number of verifying keys, according to the program.");
        }
        // Ensure the deployment contains the correct functions.
        for function_name in program.functions().keys() {
            if !deployment.verifying_keys().keys().contains(function_name) {
                bail!("Deployment is missing a verifying key for function '{function_name}'.");
            }
        }

        // Store the program ID.
        self.id_map().insert(*transaction_id, program_id)?;
        // Store the reverse program ID.
        self.reverse_id_map().insert(program_id, *transaction_id)?;
        // Store the edition.
        self.edition_map().insert(program_id, deployment.edition())?;
        // Store the program.
        self.program_map().insert(program_id, program.clone())?;

        // Store the verifying keys and certificates.
        for (function_name, (verifying_key, certificate)) in deployment.verifying_keys() {
            // Store the verifying key.
            self.verifying_key_map().insert((program_id, *function_name), verifying_key.clone())?;
            // Store the certificate.
            self.certificate_map().insert((program_id, *function_name), certificate.clone())?;
        }

        // Store the additional fee ID.
        self.additional_fee_map().insert(*transaction_id, *additional_fee.id())?;
        // Store the additional fee transition.
        self.transition_store().insert(additional_fee.clone())?;

        Ok(())
    }

    /// Removes the deployment for the given `transaction ID`.
    fn remove(&self, transaction_id: &N::TransactionID) -> Result<()> {
        // Retrieve the program ID.
        let program_id = self.get_program_id(transaction_id)?;
        // Retrieve the program.
        let program = self.get_program(&program_id)?;
        // Retrieve the additional fee ID.
        let additional_fee_id = match self.additional_fee_map().get(transaction_id)? {
            Some(additional_fee_id) => cow_to_copied!(additional_fee_id),
            None => bail!("Failed to locate the additional fee ID for transaction '{transaction_id}'"),
        };

        // Remove the program ID.
        self.id_map().remove(transaction_id)?;
        // Remove the reverse program ID.
        self.reverse_id_map().remove(&program_id)?;
        // Remove the edition.
        self.edition_map().remove(&program_id)?;
        // Remove the program.
        self.program_map().remove(&program_id)?;

        // Remove the verifying keys and certificates.
        for function_name in program.functions().keys() {
            // Remove the verifying key.
            self.verifying_key_map().remove(&(program_id, *function_name))?;
            // Remove the certificate.
            self.certificate_map().remove(&(program_id, *function_name))?;
        }

        // Remove the additional fee ID.
        self.additional_fee_map().remove(&transaction_id)?;
        // Remove the additional fee transition.
        self.transition_store().remove(&additional_fee_id)?;

        Ok(())
    }
}

/// An in-memory deployment storage.
#[derive(Clone)]
pub struct DeploymentMemory<N: Network> {
    /// The mapping of `transaction ID` to `program ID`.
    id_map: MemoryMap<N::TransactionID, ProgramID<N>>,
    /// The mapping of `program ID` to `transaction ID`.
    reverse_id_map: MemoryMap<ProgramID<N>, N::TransactionID>,
    /// The mapping of `program ID` to `edition`.
    edition_map: MemoryMap<ProgramID<N>, u16>,
    /// The mapping of `program ID` to `program`.
    program_map: MemoryMap<ProgramID<N>, Program<N>>,
    /// The mapping of `(program ID, function name)` to `verifying key`.
    verifying_key_map: MemoryMap<(ProgramID<N>, Identifier<N>), VerifyingKey<N>>,
    /// The mapping of `(program ID, function name)` to `certificate`.
    certificate_map: MemoryMap<(ProgramID<N>, Identifier<N>), Certificate<N>>,
    /// The mapping of `transaction ID` to `additional fee ID`.
    additional_fee_map: MemoryMap<N::TransactionID, N::TransitionID>,
    /// The transition store.
    transition_store: TransitionStore<N, TransitionMemory<N>>,
}

impl<N: Network> DeploymentMemory<N> {
    /// Creates a new in-memory deployment storage.
    pub fn new(transition_store: TransitionStore<N, TransitionMemory<N>>) -> Self {
        Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            edition_map: MemoryMap::default(),
            program_map: MemoryMap::default(),
            verifying_key_map: MemoryMap::default(),
            certificate_map: MemoryMap::default(),
            additional_fee_map: MemoryMap::default(),
            transition_store,
        }
    }
}

#[rustfmt::skip]
impl<N: Network> DeploymentStorage<N> for DeploymentMemory<N> {
    type IDMap = MemoryMap<N::TransactionID, ProgramID<N>>;
    type ReverseIDMap = MemoryMap<ProgramID<N>, N::TransactionID>;
    type EditionMap = MemoryMap<ProgramID<N>, u16>;
    type ProgramMap = MemoryMap<ProgramID<N>, Program<N>>;
    type VerifyingKeyMap = MemoryMap<(ProgramID<N>, Identifier<N>), VerifyingKey<N>>;
    type CertificateMap = MemoryMap<(ProgramID<N>, Identifier<N>), Certificate<N>>;
    type AdditionalFeeMap = MemoryMap<N::TransactionID, N::TransitionID>;
    type TransitionStorage = TransitionMemory<N>;

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the edition map.
    fn edition_map(&self) -> &Self::EditionMap {
        &self.edition_map
    }

    /// Returns the program map.
    fn program_map(&self) -> &Self::ProgramMap {
        &self.program_map
    }

    /// Returns the verifying key map.
    fn verifying_key_map(&self) -> &Self::VerifyingKeyMap {
        &self.verifying_key_map
    }

    /// Returns the certificate map.
    fn certificate_map(&self) -> &Self::CertificateMap {
        &self.certificate_map
    }

    /// Returns the additional fee map.
    fn additional_fee_map(&self) -> &Self::AdditionalFeeMap {
        &self.additional_fee_map
    }

    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        &self.transition_store
    }
}

/// The deployment store.
#[derive(Clone)]
pub struct DeploymentStore<N: Network, D: DeploymentStorage<N>> {
    /// The map of `transaction ID` to `program ID`.
    program_ids: D::IDMap,
    /// The edition map.
    edition: D::EditionMap,
    /// The program map.
    program: D::ProgramMap,
    /// The verifying keys map.
    verifying_keys: D::VerifyingKeyMap,
    /// The certificates map.
    certificates: D::CertificateMap,
    /// The additional fee map.
    additional_fee: D::AdditionalFeeMap,
    /// The deployment storage.
    storage: D,
}

impl<N: Network, D: DeploymentStorage<N>> DeploymentStore<N, D> {
    /// Initializes a new deployment store.
    pub fn new(storage: D) -> Self {
        Self {
            program_ids: storage.id_map().clone(),
            edition: storage.edition_map().clone(),
            program: storage.program_map().clone(),
            verifying_keys: storage.verifying_key_map().clone(),
            certificates: storage.certificate_map().clone(),
            additional_fee: storage.additional_fee_map().clone(),
            storage,
        }
    }

    /// Stores the given `deployment transaction` into storage.
    pub fn insert(&self, transaction: &Transaction<N>) -> Result<()> {
        self.storage.insert(transaction)
    }

    /// Removes the transaction for the given `transaction ID`.
    pub fn remove(&self, transaction_id: &N::TransactionID) -> Result<()> {
        self.storage.remove(transaction_id)
    }
}

impl<N: Network, D: DeploymentStorage<N>> DeploymentStore<N, D> {
    /// Returns the transaction for the given `transaction ID`.
    pub fn get_transaction(&self, transaction_id: &N::TransactionID) -> Result<Transaction<N>> {
        self.storage.get_transaction(transaction_id)
    }

    /// Returns the deployment for the given `transaction ID`.
    pub fn get_deployment(&self, transaction_id: &N::TransactionID) -> Result<Deployment<N>> {
        self.storage.get_deployment(transaction_id)
    }

    /// Returns the program ID for the given `transaction ID`.
    pub fn get_program_id(&self, transaction_id: &N::TransactionID) -> Result<ProgramID<N>> {
        self.storage.get_program_id(transaction_id)
    }

    /// Returns the program for the given `program ID`.
    pub fn get_program(&self, program_id: &ProgramID<N>) -> Result<Program<N>> {
        self.storage.get_program(program_id)
    }

    /// Returns the edition for the given `program ID`.
    pub fn get_edition(&self, program_id: &ProgramID<N>) -> Result<u16> {
        self.storage.get_edition(program_id)
    }

    /// Returns the verifying key for the given `(program ID, function name)`.
    pub fn get_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<VerifyingKey<N>> {
        self.storage.get_verifying_key(program_id, function_name)
    }

    /// Returns the certificate for the given `(program ID, function name)`.
    pub fn get_certificate(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> Result<Certificate<N>> {
        self.storage.get_certificate(program_id, function_name)
    }

    /// Returns the additional fee for the given `transaction ID`.
    pub fn get_additional_fee(&self, transaction_id: &N::TransactionID) -> Result<AdditionalFee<N>> {
        self.storage.get_additional_fee(transaction_id)
    }
}

impl<N: Network, D: DeploymentStorage<N>> DeploymentStore<N, D> {
    /// Returns the transaction ID that deployed the given `program ID`.
    pub fn find_transaction_id(&self, program_id: &ProgramID<N>) -> Result<Option<N::TransactionID>> {
        self.storage.find_transaction_id(program_id)
    }
}

impl<N: Network, D: DeploymentStorage<N>> DeploymentStore<N, D> {
    /// Returns an iterator over the program IDs, for all deployments.
    pub fn program_ids(&self) -> impl '_ + Iterator<Item = Cow<'_, ProgramID<N>>> {
        self.program_ids.values().map(|id| match id {
            Cow::Borrowed(id) => Cow::Borrowed(id),
            Cow::Owned(id) => Cow::Owned(id),
        })
    }

    /// Returns an iterator over the programs, for all deployments.
    pub fn programs(&self) -> impl '_ + Iterator<Item = Cow<'_, Program<N>>> {
        self.program.values().map(|program| match program {
            Cow::Borrowed(program) => Cow::Borrowed(program),
            Cow::Owned(program) => Cow::Owned(program),
        })
    }

    /// Returns an iterator over the `((program ID, function name), verifying key)`, for all deployments.
    pub fn verifying_keys(
        &self,
    ) -> impl '_ + Iterator<Item = (Cow<'_, (ProgramID<N>, Identifier<N>)>, Cow<'_, VerifyingKey<N>>)> {
        self.verifying_keys.iter()
    }

    /// Returns an iterator over the `((program ID, function name), certificate)`, for all deployments.
    pub fn certificates(
        &self,
    ) -> impl '_ + Iterator<Item = (Cow<'_, (ProgramID<N>, Identifier<N>)>, Cow<'_, Certificate<N>>)> {
        self.certificates.iter()
    }
}

impl<N: Network, D: DeploymentStorage<N>> DeploymentStore<N, D> {
    /// Returns `true` if the given program ID exists.
    pub fn contains_program_id(&self, program_id: &ProgramID<N>) -> bool {
        self.program_ids().contains(program_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_get_remove() {
        // Sample the deployment transaction.
        let transaction = crate::ledger::vm::test_helpers::sample_deployment_transaction();
        let transaction_id = transaction.id();

        // Initialize a new transition store.
        let transition_store = TransitionStore::new(TransitionMemory::new());
        // Initialize a new deployment store.
        let deployment_store = DeploymentMemory::new(transition_store);

        // Ensure the deployment transaction does not exist.
        assert!(deployment_store.get_transaction(&transaction_id).is_err());

        // Insert the deployment transaction.
        deployment_store.insert(&transaction).unwrap();

        // Retrieve the deployment transaction.
        let candidate = deployment_store.get_transaction(&transaction_id).unwrap();
        assert_eq!(transaction, candidate);

        // Remove the deployment.
        deployment_store.remove(&transaction_id).unwrap();

        // Ensure the deployment transaction does not exist.
        assert!(deployment_store.get_transaction(&transaction_id).is_err());
    }

    #[test]
    fn test_find_transaction_id() {
        // Sample the deployment transaction.
        let transaction = crate::ledger::vm::test_helpers::sample_deployment_transaction();
        let transaction_id = transaction.id();
        let program_id = match transaction {
            Transaction::Deploy(_, ref deployment, _) => *deployment.program_id(),
            _ => panic!("Incorrect transaction type"),
        };

        // Initialize a new transition store.
        let transition_store = TransitionStore::new(TransitionMemory::new());
        // Initialize a new deployment store.
        let deployment_store = DeploymentMemory::new(transition_store);

        // Ensure the deployment transaction does not exist.
        assert!(deployment_store.get_transaction(&transaction_id).is_err());

        // Ensure the transaction ID is not found.
        let candidate = deployment_store.find_transaction_id(&program_id).unwrap();
        assert_eq!(None, candidate);

        // Insert the deployment.
        deployment_store.insert(&transaction).unwrap();

        // Find the transaction ID.
        let candidate = deployment_store.find_transaction_id(&program_id).unwrap();
        assert_eq!(Some(transaction_id), candidate);

        // Remove the deployment.
        deployment_store.remove(&transaction_id).unwrap();

        // Ensure the transaction ID is not found.
        let candidate = deployment_store.find_transaction_id(&program_id).unwrap();
        assert_eq!(None, candidate);
    }
}
