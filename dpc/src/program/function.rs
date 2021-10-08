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

use crate::{CircuitLogic, FunctionType, Network, ProgramError, PublicVariables};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum Function<N: Network> {
    Noop,
    Circuit(
        N::FunctionID,
        Arc<dyn CircuitLogic<N>>,
        <N::ProgramSNARK as SNARK>::ProvingKey,
        <N::ProgramSNARK as SNARK>::VerifyingKey,
    ),
}

impl<N: Network> Function<N> {
    /// Initializes a new instance of the function.
    pub fn new(logic: Arc<dyn CircuitLogic<N>>) -> Result<Self, ProgramError> {
        // Compute the proving key and verifying key.
        let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
            &SynthesizedCircuit::Blank(logic.clone()),
            &mut *N::program_srs(&mut rand::thread_rng()).borrow_mut(),
        )?;

        // Compute the circuit ID.
        let circuit_id = <N as Network>::function_id(&verifying_key)?;

        Ok(Self::Circuit(circuit_id, logic, proving_key, verifying_key))
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        match self {
            Self::Noop => *N::noop_circuit_id(),
            Self::Circuit(circuit_id, _, _, _) => *circuit_id,
        }
    }

    /// Returns the function type.
    pub fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Circuit(_, logic, _, _) => logic.function_type(),
        }
    }

    /// Returns the function proving key.
    pub fn proving_key(&self) -> &<N::ProgramSNARK as SNARK>::ProvingKey {
        match self {
            Self::Noop => N::noop_circuit_proving_key(),
            Self::Circuit(_, _, proving_key, _) => &proving_key,
        }
    }

    /// Returns the function verifying key.
    pub fn verifying_key(&self) -> &<N::ProgramSNARK as SNARK>::VerifyingKey {
        match self {
            Self::Noop => N::noop_circuit_verifying_key(),
            Self::Circuit(_, _, _, verifying_key) => &verifying_key,
        }
    }

    /// Returns the native evaluation of the function on given public and private variables.
    fn evaluate(&self, _public: PublicVariables<N>) -> bool {
        unimplemented!("The native evaluation of this function is unimplemented")
    }

    /// Returns true if the execution of the function is valid.
    pub fn verify(&self, public: PublicVariables<N>, proof: &<N::ProgramSNARK as SNARK>::Proof) -> bool {
        <N::ProgramSNARK as SNARK>::verify(self.verifying_key(), &public, proof)
            .expect("Failed to verify function execution proof")
    }

    /// Returns the assigned circuit.
    pub(crate) fn synthesize(&self, public: PublicVariables<N>) -> SynthesizedCircuit<N> {
        match self {
            Self::Noop => SynthesizedCircuit::Noop(public),
            Self::Circuit(_, logic, _, _) => SynthesizedCircuit::Assigned(logic.clone(), public),
        }
    }
}

// TODO (howardwu): TEMPORARY - Guard access to this enum, to prevent abuse of it.
pub enum SynthesizedCircuit<N: Network> {
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
                let _position = UInt8::alloc_input_vec_le(cs.ns(|| "Alloc position"), &[0u8])?;

                let _transaction_id_crh = N::TransactionIDCRHGadget::alloc_constant(
                    &mut cs.ns(|| "Declare the transaction ID CRH scheme"),
                    || Ok(N::transaction_id_crh().clone()),
                )?;

                let _transaction_id = <N::TransactionIDCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
                    cs.ns(|| "Alloc the transaction ID"),
                    || Ok(public.transaction_id),
                )?;

                Ok(())
            }
            Self::Blank(logic) => {
                let synthesizer = Self::Assigned(logic.clone(), Default::default());
                synthesizer.generate_constraints(cs)
            }
            Self::Assigned(_logic, _public) => {
                // TODO (howardwu): Add any DPC related safety checks around program executions.
                unimplemented!()
                // logic.synthesize::<CS>(cs, public)
            }
        }
    }
}
