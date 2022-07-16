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

use crate::{ProvingKey, UniversalSRS, VerifyingKey};
use console::{
    network::prelude::*,
    program::{Identifier, ProgramID},
};

use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use parking_lot::RwLock;
use std::sync::Arc;

#[derive(Clone, Default)]
#[allow(clippy::type_complexity)]
pub struct CircuitKeys<N: Network> {
    /// The universal SRS.
    universal_srs: Arc<OnceCell<UniversalSRS<N>>>,
    /// The mapping of `(program ID, function name)` to proving key.
    proving_keys: Arc<RwLock<IndexMap<(ProgramID<N>, Identifier<N>), ProvingKey<N>>>>,
    /// The mapping of `(program ID, function name)` to verifying key.
    verifying_keys: Arc<RwLock<IndexMap<(ProgramID<N>, Identifier<N>), VerifyingKey<N>>>>,
}

impl<N: Network> CircuitKeys<N> {
    /// Initialize a new `CircuitKeys` instance.
    pub fn new() -> Self {
        Self {
            universal_srs: Arc::new(OnceCell::new()),
            proving_keys: Default::default(),
            verifying_keys: Default::default(),
        }
    }

    /// Returns `true` if the proving key for the given program ID and function name exists.
    pub fn contains_proving_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> bool {
        self.proving_keys.read().contains_key(&(*program_id, *function_name))
    }

    /// Returns `true` if the verifying key for the given program ID and function name exists.
    pub fn contains_verifying_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> bool {
        self.verifying_keys.read().contains_key(&(*program_id, *function_name))
    }

    /// Returns the proving key for the given program ID and function name.
    pub fn get_proving_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> Result<ProvingKey<N>> {
        match self.proving_keys.read().get(&(*program_id, *function_name)) {
            Some(proving_key) => Ok(proving_key.clone()),
            None => bail!("Proving key not found for: {program_id} {function_name}"),
        }
    }

    /// Returns the verifying key for the given program ID and function name.
    pub fn get_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<VerifyingKey<N>> {
        match self.verifying_keys.read().get(&(*program_id, *function_name)) {
            Some(verifying_key) => Ok(verifying_key.clone()),
            None => bail!("Verifying key not found for: {program_id} {function_name}"),
        }
    }

    /// Inserts the given proving key for the given program ID and function name.
    pub fn insert_proving_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        proving_key: ProvingKey<N>,
    ) {
        self.proving_keys.write().insert((*program_id, *function_name), proving_key);
    }

    /// Inserts the given verifying key for the given program ID and function name.
    pub fn insert_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        verifying_key: VerifyingKey<N>,
    ) {
        self.verifying_keys.write().insert((*program_id, *function_name), verifying_key);
    }

    /// Inserts the derived `(proving_key, verifying_key)` for the given program ID, function name, and assignment.
    pub fn insert_from_assignment(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        assignment: &circuit::Assignment<N::Field>,
    ) -> Result<()> {
        let universal_srs = self.universal_srs.get_or_try_init(|| UniversalSRS::load())?;
        let (proving_key, verifying_key) = universal_srs.to_circuit_key(function_name, assignment)?;
        // Insert the proving key.
        self.insert_proving_key(program_id, function_name, proving_key);
        // Insert the verifying key.
        self.insert_verifying_key(program_id, function_name, verifying_key);
        Ok(())
    }

    /// Removes the proving and verifying key for the given program ID and function name.
    pub fn remove(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) {
        self.proving_keys.write().remove(&(*program_id, *function_name));
        self.verifying_keys.write().remove(&(*program_id, *function_name));
    }
}
