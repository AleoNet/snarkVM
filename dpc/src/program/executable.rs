// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{CircuitType, Network, ProgramCircuit, ProgramError, ProgramExecutable, PublicVariables};
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};

use anyhow::Result;

/// Program ID, program path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Execution<N: Network> {
    pub program_id: N::ProgramID,
    pub program_path: MerklePath<N::ProgramCircuitsTreeParameters>,
    pub verifying_key: <N::ProgramSNARK as SNARK>::VerifyingKey,
    pub proof: <N::ProgramSNARK as SNARK>::Proof,
}

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum Executable<N: Network> {
    Noop,
    Circuit(
        N::ProgramID,
        ProgramCircuit<N>,
        MerklePath<N::ProgramCircuitsTreeParameters>,
    ),
}

impl<N: Network> ProgramExecutable<N> for Executable<N> {
    fn new(
        program_id: N::ProgramID,
        circuit: ProgramCircuit<N>,
        program_path: MerklePath<N::ProgramCircuitsTreeParameters>,
    ) -> Result<Self, ProgramError> {
        assert!(program_path.verify(&program_id, &circuit.circuit_id())?);
        Ok(Self::Circuit(program_id, circuit, program_path))
    }

    /// Returns the program ID of the executable.
    fn program_id(&self) -> N::ProgramID {
        match self {
            Self::Noop => *N::noop_program_id(),
            Self::Circuit(program_id, _, _) => *program_id,
        }
    }

    /// Returns the circuit ID of the executable.
    fn circuit_id(&self) -> N::ProgramCircuitID {
        match self {
            Self::Noop => *N::noop_circuit_id(),
            Self::Circuit(_, circuit, _) => circuit.circuit_id(),
        }
    }

    /// Returns the circuit type of the executable.
    fn circuit_type(&self) -> CircuitType {
        match self {
            Self::Noop => CircuitType::Noop,
            Self::Circuit(_, circuit, _) => circuit.circuit_type(),
        }
    }

    /// Executes the circuit, returning an proof.
    fn execute(&self, public: PublicVariables<N>) -> Result<Execution<N>, ProgramError> {
        let (circuit, verifying_key, program_path) = match self {
            Self::Noop => (
                &ProgramCircuit::Noop,
                N::noop_circuit_verifying_key().clone(),
                N::noop_program_path().clone(),
            ),
            Self::Circuit(_, circuit, program_path) => (circuit, circuit.verifying_key().clone(), program_path.clone()),
        };

        // Compute the proof.
        let proof = <N::ProgramSNARK as SNARK>::prove(
            circuit.proving_key(),
            &circuit.synthesize(public.clone()),
            &mut rand::thread_rng(),
        )?;
        assert!(self.verify(public, &proof));

        Ok(Execution {
            program_id: self.program_id(),
            program_path,
            verifying_key,
            proof,
        })
    }

    /// Returns true if the execution of the circuit is valid.
    fn verify(&self, public: PublicVariables<N>, proof: &<N::ProgramSNARK as SNARK>::Proof) -> bool {
        // Fetch the verifying key.
        let verifying_key = match self {
            Self::Noop => ProgramCircuit::<N>::Noop.verifying_key(),
            Self::Circuit(_, circuit, _) => circuit.verifying_key(),
        };

        <N::ProgramSNARK as SNARK>::verify(&verifying_key, &public, proof)
            .expect("Failed to verify program execution proof")
    }
}
