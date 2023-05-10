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
        helpers::rocksdb::{
            self,
            DataMap,
            Database,
            DeploymentMap,
            ExecutionMap,
            FeeMap,
            MapID,
            TransactionMap,
            TransitionDB,
        },
        DeploymentStorage,
        DeploymentStore,
        ExecutionStorage,
        ExecutionStore,
        FeeStorage,
        FeeStore,
        TransactionStorage,
        TransactionType,
        TransitionStore,
    },
};
use console::{
    prelude::*,
    program::{Identifier, ProgramID, ProgramOwner},
};

/// A database transaction storage.
#[derive(Clone)]
pub struct TransactionDB<N: Network> {
    /// The mapping of `transaction ID` to `transaction type`.
    id_map: DataMap<N::TransactionID, TransactionType>,
    /// The deployment store.
    deployment_store: DeploymentStore<N, DeploymentDB<N>>,
    /// The execution store.
    execution_store: ExecutionStore<N, ExecutionDB<N>>,
    /// The fee store.
    fee_store: FeeStore<N, FeeDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> TransactionStorage<N> for TransactionDB<N> {
    type IDMap = DataMap<N::TransactionID, TransactionType>;
    type DeploymentStorage = DeploymentDB<N>;
    type ExecutionStorage = ExecutionDB<N>;
    type FeeStorage = FeeDB<N>;
    type TransitionStorage = TransitionDB<N>;

    /// Initializes the transaction storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        // Initialize the fee store.
        let fee_store = FeeStore::<N, FeeDB<N>>::open(transition_store)?;
        // Initialize the deployment store.
        let deployment_store = DeploymentStore::<N, DeploymentDB<N>>::open(fee_store.clone())?;
        // Initialize the execution store.
        let execution_store = ExecutionStore::<N, ExecutionDB<N>>::open(fee_store.clone())?;
        // Return the transaction storage.
        Ok(Self { id_map: rocksdb::RocksDB::open_map(N::ID, execution_store.dev(), MapID::Transaction(TransactionMap::ID))?, deployment_store, execution_store, fee_store })
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

    /// Returns the fee store.
    fn fee_store(&self) -> &FeeStore<N, Self::FeeStorage> {
        &self.fee_store
    }
}

/// A database deployment storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct DeploymentDB<N: Network> {
    /// The ID map.
    id_map: DataMap<N::TransactionID, ProgramID<N>>,
    /// The edition map.
    edition_map: DataMap<ProgramID<N>, u16>,
    /// The reverse ID map.
    reverse_id_map: DataMap<(ProgramID<N>, u16), N::TransactionID>,
    /// The program owner map.
    owner_map: DataMap<(ProgramID<N>, u16), ProgramOwner<N>>,
    /// The program map.
    program_map: DataMap<(ProgramID<N>, u16), Program<N>>,
    /// The verifying key map.
    verifying_key_map: DataMap<(ProgramID<N>, Identifier<N>, u16), VerifyingKey<N>>,
    /// The certificate map.
    certificate_map: DataMap<(ProgramID<N>, Identifier<N>, u16), Certificate<N>>,
    /// The fee store.
    fee_store: FeeStore<N, FeeDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> DeploymentStorage<N> for DeploymentDB<N> {
    type IDMap = DataMap<N::TransactionID, ProgramID<N>>;
    type EditionMap = DataMap<ProgramID<N>, u16>;
    type ReverseIDMap = DataMap<(ProgramID<N>, u16), N::TransactionID>;
    type OwnerMap = DataMap<(ProgramID<N>, u16), ProgramOwner<N>>;
    type ProgramMap = DataMap<(ProgramID<N>, u16), Program<N>>;
    type VerifyingKeyMap = DataMap<(ProgramID<N>, Identifier<N>, u16), VerifyingKey<N>>;
    type CertificateMap = DataMap<(ProgramID<N>, Identifier<N>, u16), Certificate<N>>;
    type FeeStorage = FeeDB<N>;

    /// Initializes the deployment storage.
    fn open(fee_store: FeeStore<N, Self::FeeStorage>) -> Result<Self> {
        // Retrieve the optional development ID.
        let dev = fee_store.dev();
        Ok(Self {
            id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::ID))?,
            edition_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::Edition))?,
            reverse_id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::ReverseID))?,
            owner_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::Owner))?,
            program_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::Program))?,
            verifying_key_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::VerifyingKey))?,
            certificate_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Deployment(DeploymentMap::Certificate))?,
            fee_store,
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

    /// Returns the program owner map.
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

    /// Returns the fee store.
    fn fee_store(&self) -> &FeeStore<N, Self::FeeStorage> {
        &self.fee_store
    }
}

/// A database execution storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct ExecutionDB<N: Network> {
    /// The ID map.
    id_map: DataMap<N::TransactionID, (Vec<N::TransitionID>, bool)>,
    /// The reverse ID map.
    reverse_id_map: DataMap<N::TransitionID, N::TransactionID>,
    /// The inclusion map.
    inclusion_map: DataMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>,
    /// The fee store.
    fee_store: FeeStore<N, FeeDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> ExecutionStorage<N> for ExecutionDB<N> {
    type IDMap = DataMap<N::TransactionID, (Vec<N::TransitionID>, bool)>;
    type ReverseIDMap = DataMap<N::TransitionID, N::TransactionID>;
    type InclusionMap = DataMap<N::TransactionID, (N::StateRoot, Option<Proof<N>>)>;
    type FeeStorage = FeeDB<N>;

    /// Initializes the execution storage.
    fn open(fee_store: FeeStore<N, Self::FeeStorage>) -> Result<Self> {
        // Retrieve the optional development ID.
        let dev = fee_store.dev();
        Ok(Self {
            id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Execution(ExecutionMap::ID))?,
            reverse_id_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Execution(ExecutionMap::ReverseID))?,
            inclusion_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Execution(ExecutionMap::Inclusion))?,
            fee_store,
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

    /// Returns the inclusion map.
    fn inclusion_map(&self) -> &Self::InclusionMap {
        &self.inclusion_map
    }

    /// Returns the fee store.
    fn fee_store(&self) -> &FeeStore<N, Self::FeeStorage> {
        &self.fee_store
    }
}

/// A database for fee storage.
#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct FeeDB<N: Network> {
    /// The fee map.
    fee_map: DataMap<N::TransactionID, (N::TransitionID, N::StateRoot, Option<Proof<N>>)>,
    /// The reverse fee map.
    reverse_fee_map: DataMap<N::TransitionID, N::TransactionID>,
    /// The transition store.
    transition_store: TransitionStore<N, TransitionDB<N>>,
}

#[rustfmt::skip]
impl<N: Network> FeeStorage<N> for FeeDB<N> {
    type FeeMap = DataMap<N::TransactionID, (N::TransitionID, N::StateRoot, Option<Proof<N>>)>;
    type ReverseFeeMap = DataMap<N::TransitionID, N::TransactionID>;
    type TransitionStorage = TransitionDB<N>;

    /// Initializes the fee storage.
    fn open(transition_store: TransitionStore<N, Self::TransitionStorage>) -> Result<Self> {
        // Retrieve the optional development ID.
        let dev = transition_store.dev();
        Ok(Self {
            fee_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Fee(FeeMap::Fee))?,
            reverse_fee_map: rocksdb::RocksDB::open_map(N::ID, dev, MapID::Fee(FeeMap::ReverseFee))?,
            transition_store,
        })
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
