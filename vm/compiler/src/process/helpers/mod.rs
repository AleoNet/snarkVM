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

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct CircuitKeys<N: Network> {
    /// The universal SRS.
    universal_srs: Arc<OnceCell<UniversalSRS<N>>>,
    /// The mapping of `(program ID, function name)` to `(proving_key, verifying_key)`.
    circuit_keys: Arc<RwLock<IndexMap<(ProgramID<N>, Identifier<N>), (ProvingKey<N>, VerifyingKey<N>)>>>,
}

impl<N: Network> CircuitKeys<N> {
    /// Initialize a new `CircuitKeys` instance.
    pub fn new() -> Self {
        Self { universal_srs: Arc::new(OnceCell::new()), circuit_keys: Arc::new(RwLock::new(IndexMap::new())) }
    }

    /// Returns `true` if the given program ID and function name exists.
    pub fn contains_key(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) -> bool {
        self.circuit_keys.read().contains_key(&(*program_id, *function_name))
    }

    /// Returns the `(proving_key, verifying_key)` for the given program ID and function name.
    pub fn get(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
    ) -> Result<(ProvingKey<N>, VerifyingKey<N>)> {
        self.circuit_keys
            .read()
            .get(&(*program_id, *function_name))
            .cloned()
            .ok_or_else(|| anyhow!("Circuit key not found: {program_id} {function_name}"))
    }

    /// Inserts the given `(proving_key, verifying_key)` for the given program ID and function name.
    pub fn insert(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        proving_key: ProvingKey<N>,
        verifying_key: VerifyingKey<N>,
    ) {
        self.circuit_keys.write().insert((*program_id, *function_name), (proving_key, verifying_key));
    }

    /// Inserts the derived `(proving_key, verifying_key)` for the given program ID, function name, and assignment.
    pub fn insert_from_assignment(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        assignment: &circuit::Assignment<N::Field>,
    ) -> Result<()> {
        // TODO (howardwu): Load the universal SRS remotely.
        let (proving_key, verifying_key) =
            self.universal_srs.get_or_try_init(|| UniversalSRS::load(100_000))?.to_circuit_key(assignment)?;
        // Insert the proving key and verifying key.
        self.insert(program_id, function_name, proving_key, verifying_key);
        Ok(())
    }

    /// Removes the given program ID and function name.
    pub fn remove(&self, program_id: &ProgramID<N>, function_name: &Identifier<N>) {
        self.circuit_keys.write().remove(&(*program_id, *function_name));
    }

    /// Returns the number of circuit keys.
    pub fn len(&self) -> usize {
        self.circuit_keys.read().len()
    }

    /// Returns `true` if there are no circuit keys.
    pub fn is_empty(&self) -> bool {
        self.circuit_keys.read().is_empty()
    }
}
impl<N: Network> Default for CircuitKeys<N> {
    fn default() -> Self {
        Self::new()
    }
}
