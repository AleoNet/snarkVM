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

use crate::{CircuitError, CircuitLogic, CircuitType, LocalData, Network, PublicVariables};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum ProgramCircuit<N: Network> {
    Noop,
    Circuit(
        N::ProgramCircuitID,
        Arc<dyn CircuitLogic<N>>,
        <N::ProgramSNARK as SNARK>::ProvingKey,
        <N::ProgramSNARK as SNARK>::VerifyingKey,
    ),
}

impl<N: Network> ProgramCircuit<N> {
    /// Initializes a new instance of the circuit.
    pub fn new(logic: Arc<dyn CircuitLogic<N>>) -> Result<Self, CircuitError> {
        // Compute the proving key and verifying key.
        let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
            &SynthesizedCircuit::Blank(logic.clone()),
            &mut *N::program_srs(&mut rand::thread_rng()).borrow_mut(),
        )?;

        // Compute the circuit ID.
        let circuit_id = <N as Network>::program_circuit_id(&verifying_key)?;

        Ok(Self::Circuit(circuit_id, logic, proving_key, verifying_key))
    }

    /// Returns the circuit ID.
    pub fn circuit_id(&self) -> N::ProgramCircuitID {
        match self {
            Self::Noop => *N::noop_circuit_id(),
            Self::Circuit(circuit_id, _, _, _) => *circuit_id,
        }
    }

    /// Returns the circuit type.
    pub fn circuit_type(&self) -> CircuitType {
        match self {
            Self::Noop => CircuitType::Noop,
            Self::Circuit(_, logic, _, _) => logic.circuit_type(),
        }
    }

    /// Returns the circuit proving key.
    pub fn proving_key(&self) -> &<N::ProgramSNARK as SNARK>::ProvingKey {
        match self {
            Self::Noop => N::noop_circuit_proving_key(),
            Self::Circuit(_, _, proving_key, _) => &proving_key,
        }
    }

    /// Returns the circuit verifying key.
    pub fn verifying_key(&self) -> &<N::ProgramSNARK as SNARK>::VerifyingKey {
        match self {
            Self::Noop => N::noop_circuit_verifying_key(),
            Self::Circuit(_, _, _, verifying_key) => &verifying_key,
        }
    }

    /// Returns the assigned circuit.
    pub(crate) fn synthesize(&self, public: PublicVariables<N>, _local_data: &LocalData<N>) -> SynthesizedCircuit<N> {
        match self {
            Self::Noop => SynthesizedCircuit::Noop(public),
            Self::Circuit(_, logic, _, _) => SynthesizedCircuit::Assigned(logic.clone(), public),
        }
    }
}

pub(crate) enum SynthesizedCircuit<N: Network> {
    Noop(PublicVariables<N>),
    Blank(Arc<dyn CircuitLogic<N>>),
    Assigned(Arc<dyn CircuitLogic<N>>, PublicVariables<N>),
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for SynthesizedCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        match self {
            Self::Noop(public) => {
                let _record_position =
                    UInt8::alloc_input_vec_le(cs.ns(|| "Alloc record position"), &[public.record_position])?;

                let _local_data_commitment_scheme = N::LocalDataCommitmentGadget::alloc_constant(
                    &mut cs.ns(|| "Declare the local data commitment scheme"),
                    || Ok(N::local_data_commitment_scheme().clone()),
                )?;

                let _local_data_root = <N::LocalDataCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
                    cs.ns(|| "Alloc local data root"),
                    || Ok(public.local_data_root),
                )?;

                Ok(())
            }
            Self::Blank(logic) => {
                let synthesizer = Self::Assigned(logic.clone(), Default::default());
                synthesizer.generate_constraints(cs)
            }
            Self::Assigned(logic, public) => {
                // TODO (howardwu): Add any DPC related safety checks around program executions.
                unimplemented!()
                // logic.synthesize::<CS>(cs, public)
            }
        }
    }
}
