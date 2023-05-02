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
mod serialize;
mod string;

// use circuit::{Aleo, Identifier};
use crate::{process::Identifier, snark::Proof, Input, KeyBatch, Transition};
use circuit::Assignment;
use console::{
    network::prelude::*,
    program::{Literal, Plaintext},
    types::U64,
};

#[derive(Clone, PartialEq, Eq)]
pub struct Fee<N: Network> {
    /// The transition.
    transition: Transition<N>,
    /// The global state root.
    global_state_root: N::StateRoot,
    /// The proof of transition and optional inclusion.
    proof: Option<Proof<N>>,
}

impl<N: Network> Fee<N> {
    /// Initializes a new `Fee` instance with the given transition, global state root, and inclusion proof.
    pub fn from(transition: Transition<N>, global_state_root: N::StateRoot, proof: Option<Proof<N>>) -> Self {
        // Return the new `Fee` instance.
        Self { transition, global_state_root, proof }
    }

    /// Returns 'true' if the fee amount is zero.
    pub fn is_zero(&self) -> Result<bool> {
        self.amount().map(|amount| amount.is_zero())
    }

    /// Returns the amount (in microcredits).
    pub fn amount(&self) -> Result<U64<N>> {
        // Retrieve the amount (in microcredits) as a plaintext value.
        match self.transition.inputs().get(1) {
            Some(Input::Public(_, Some(Plaintext::Literal(Literal::U64(microcredits), _)))) => Ok(*microcredits),
            _ => bail!("Failed to retrieve the fee (in microcredits) from the fee transition"),
        }
    }

    /// Returns the transition ID.
    pub fn transition_id(&self) -> &N::TransitionID {
        self.transition.id()
    }

    /// Returns the transition.
    pub const fn transition(&self) -> &Transition<N> {
        &self.transition
    }

    /// Returns the transition, consuming self in the process.
    pub fn into_transition(self) -> Transition<N> {
        self.transition
    }

    /// Returns the global state root.
    pub const fn global_state_root(&self) -> N::StateRoot {
        self.global_state_root
    }

    /// Returns whether the fee proves inclusion
    pub fn proves_inclusion(&self) -> bool {
        if let Some(proof) = &self.proof { proof.proves_inclusion() } else { false }
    }

    /// Returns the fee proof.
    pub const fn proof(&self) -> Option<&Proof<N>> {
        self.proof.as_ref()
    }

    pub fn prove<R: Rng + CryptoRng>(
        &mut self,
        batch: KeyBatch<N>,
        assignments: &[&Vec<&Assignment<N::Field>>],
        function_names: Vec<&Identifier<N>>,
        rng: &mut R,
    ) -> Result<()> {
        if assignments.is_empty() || assignments.len() > 2 {
            bail!("Expected 1 or 2 assignments, got {}", assignments.len())
        }
        let inclusion_name = Identifier::<N>::from_str(N::INCLUSION_FUNCTION_NAME)?;
        if assignments.len() == 2 && *function_names[1] != inclusion_name {
            bail!("Expected 2nd assignment to belong to inclusion")
        }
        let proves_inclusion = *function_names[function_names.len() - 1] == inclusion_name;
        let proof = batch.prove(function_names.as_slice(), assignments, proves_inclusion, rng)?;

        self.proof = Some(proof);

        Ok(())
    }

    /// Verifies the fee.
    pub fn verify(&self, batch: KeyBatch<N>, inputs: &[Vec<Vec<N::Field>>]) -> Result<bool> {
        if self.proof.is_none() {
            bail!("Proof missing!")
        }
        let mut function_names = vec![self.transition().function_name()];
        let inclusion_name = Identifier::<N>::from_str(N::INCLUSION_FUNCTION_NAME)?;
        if inputs.len() > 1 {
            function_names.push(&inclusion_name);
        }
        batch.verify(function_names.as_slice(), inputs, self.proof.as_ref().unwrap())?;

        Ok(true)
    }
}

impl<N: Network> Deref for Fee<N> {
    type Target = Transition<N>;

    fn deref(&self) -> &Self::Target {
        &self.transition
    }
}
