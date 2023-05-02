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

use crate::{
    program::Program,
    snark::{Certificate, Proof, VerifyingKey},
    store::{
        helpers::memory::{MemoryMap, TransitionMemory},
        DeploymentStorage,
        DeploymentStore,
        ExecutionStorage,
        ExecutionStore,
        TransactionStorage,
        TransactionType,
        TransitionStore,
    },
};
use console::{
    prelude::*,
    program::{Identifier, ProgramID, ProgramOwner},
};

/// An in-memory transaction storage.
#[derive(Clone)]
pub struct TransactionMemory<N: Network> {
    /// The mapping of `transaction ID` to `transaction type`.
    id_map: MemoryMap<N::TransactionID, TransactionType>,
    /// The deployment store.
    deployment_store: DeploymentStore<N, DeploymentMemory<N>>,
    /// The execution store.
    execution_store: ExecutionStore<N, ExecutionMemory<N>>,
}

#[rustfmt::skip]
impl<N: Network> TransactionStorage<N> for TransactionMemory<N> {
    type IDMap = MemoryMap<N::TransactionID, TransactionType>;
    type DeploymentStorage = DeploymentMemory<N>;
    type ExecutionStorage = ExecutionMemory<N>;
    type TransitionStorage = TransitionMemory<N>;

    /// Initializes the transaction storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        // Initialize the deployment store.
        let deployment_store = DeploymentStore::<N, DeploymentMemory<N>>::open(transition_store.clone())?;
        // Initialize the execution store.
        let execution_store = ExecutionStore::<N, ExecutionMemory<N>>::open(transition_store)?;
        // Return the transaction storage.
        Ok(Self { id_map: MemoryMap::default(), deployment_store, execution_store })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the deployment store.
    fn deployment_store(&self) -> &DeploymentStore<N, Self::DeploymentStorage> {
        &self.deployment_store
    }

    /// Returns the execution store.
    fn execution_store(&self) -> &ExecutionStore<N, Self::ExecutionStorage> {
        &self.execution_store
    }
}

/// An in-memory deployment storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct DeploymentMemory<N: Network> {
    /// The ID map.
    id_map: MemoryMap<N::TransactionID, ProgramID<N>>,
    /// The edition map.
    edition_map: MemoryMap<ProgramID<N>, u16>,
    /// The reverse ID map.
    reverse_id_map: MemoryMap<(ProgramID<N>, u16), N::TransactionID>,
    /// The owner map.
    owner_map: MemoryMap<(ProgramID<N>, u16), ProgramOwner<N>>,
    /// The program map.
    program_map: MemoryMap<(ProgramID<N>, u16), Program<N>>,
    /// The verifying key map.
    verifying_key_map: MemoryMap<(ProgramID<N>, Identifier<N>, u16), VerifyingKey<N>>,
    /// The certificate map.
    certificate_map: MemoryMap<(ProgramID<N>, Identifier<N>, u16), Certificate<N>>,
    /// The fee map.
    fee_map: MemoryMap<N::TransactionID, (N::TransitionID, N::StateRoot, Option<Proof<N>>)>,
    /// The reverse fee map.
    reverse_fee_map: MemoryMap<N::TransitionID, N::TransactionID>,
    /// The transition store.
    transition_store: TransitionStore<N, TransitionMemory<N>>,
}

#[rustfmt::skip]
impl<N: Network> DeploymentStorage<N> for DeploymentMemory<N> {
    type IDMap = MemoryMap<N::TransactionID, ProgramID<N>>;
    type EditionMap = MemoryMap<ProgramID<N>, u16>;
    type ReverseIDMap = MemoryMap<(ProgramID<N>, u16), N::TransactionID>;
    type OwnerMap = MemoryMap<(ProgramID<N>, u16), ProgramOwner<N>>;
    type ProgramMap = MemoryMap<(ProgramID<N>, u16), Program<N>>;
    type VerifyingKeyMap = MemoryMap<(ProgramID<N>, Identifier<N>, u16), VerifyingKey<N>>;
    type CertificateMap = MemoryMap<(ProgramID<N>, Identifier<N>, u16), Certificate<N>>;
    type FeeMap = MemoryMap<N::TransactionID, (N::TransitionID, N::StateRoot, Option<Proof<N>>)>;
    type ReverseFeeMap = MemoryMap<N::TransitionID, N::TransactionID>;
    type TransitionStorage = TransitionMemory<N>;

    /// Initializes the deployment storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        Ok(Self {
            id_map: MemoryMap::default(),
            edition_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            owner_map: MemoryMap::default(),
            program_map: MemoryMap::default(),
            verifying_key_map: MemoryMap::default(),
            certificate_map: MemoryMap::default(),
            fee_map: MemoryMap::default(),
            reverse_fee_map: MemoryMap::default(),
            transition_store,
        })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the edition map.
    fn edition_map(&self) -> &Self::EditionMap {
        &self.edition_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the owner map.
    fn owner_map(&self) -> &Self::OwnerMap {
        &self.owner_map
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

    /// Returns the fee map.
    fn fee_map(&self) -> &Self::FeeMap {
        &self.fee_map
    }

    /// Returns the reverse fee map.
    fn reverse_fee_map(&self) -> &Self::ReverseFeeMap {
        &self.reverse_fee_map
    }

    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        &self.transition_store
    }
}

/// An in-memory execution storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct ExecutionMemory<N: Network> {
    /// The ID map.
    id_map: MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>,
    /// The reverse ID map.
    reverse_id_map: MemoryMap<N::TransitionID, N::TransactionID>,
    /// The transition store.
    transition_store: TransitionStore<N, TransitionMemory<N>>,
    /// The inclusion map.
    inclusion_map: MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>,
    /// The fee map.
    fee_map: MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>,
}

#[rustfmt::skip]
impl<N: Network> ExecutionStorage<N> for ExecutionMemory<N> {
    type IDMap = MemoryMap<N::TransactionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
    type ReverseIDMap = MemoryMap<N::TransitionID, N::TransactionID>;
    type TransitionStorage = TransitionMemory<N>;
    type InclusionMap = MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;
    type FeeMap = MemoryMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;

    /// Initializes the execution storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        Ok(Self {
            id_map: MemoryMap::default(),
            reverse_id_map: MemoryMap::default(),
            transition_store,
            inclusion_map: MemoryMap::default(),
            fee_map: MemoryMap::default(),
        })
    }

    /// Returns the ID map.
    fn id_map(&self) -> &Self::IDMap {
        &self.id_map
    }

    /// Returns the reverse ID map.
    fn reverse_id_map(&self) -> &Self::ReverseIDMap {
        &self.reverse_id_map
    }

    /// Returns the transition store.
    fn transition_store(&self) -> &TransitionStore<N, Self::TransitionStorage> {
        &self.transition_store
    }

    /// Returns the inclusion map.
    fn inclusion_map(&self) -> &Self::InclusionMap {
        &self.inclusion_map
    }

    /// Returns the fee map.
    fn fee_map(&self) -> &Self::FeeMap {
        &self.fee_map
    }
}
