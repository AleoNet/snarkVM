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

use crate::{FunctionLogic, FunctionType, Network, PrivateVariables, ProgramError, PublicVariables, Record};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use rand::thread_rng;
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum Function<N: Network> {
    Noop,
    // Function(
    //     N::FunctionID,
    //     Arc<dyn FunctionLogic<N>>,
    // ),
    Function(
        N::FunctionID,
        Arc<dyn FunctionLogic<N>>,
        N::FunctionProvingKey,
        N::FunctionVerifyingKey,
    ),
}

impl<N: Network> Function<N> {
    /// Initializes a new instance of the function.
    pub fn new(logic: Arc<dyn FunctionLogic<N>>) -> Result<Self, ProgramError> {
        // Compute the proving key and verifying key.
        let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
            &SynthesizedCircuit::Blank(logic.clone()),
            &mut *N::program_srs(&mut thread_rng()).borrow_mut(),
        )?;

        // Compute the function ID.
        let function_id = <N as Network>::function_id(&verifying_key)?;

        Ok(Self::Function(function_id, logic, proving_key, verifying_key))
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        match self {
            Self::Noop => *N::noop_function_id(),
            Self::Function(circuit_id, _, _, _) => *circuit_id,
        }
    }

    // /// Returns the function logic.
    // pub fn function_logic(&self) -> &Arc<dyn FunctionLogic<N>> {
    //     match self {
    //         Self::Noop => FunctionType::Noop,
    //         Self::Function(_, logic, _, _) => logic,
    //     }
    // }

    /// Returns the function type.
    pub fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Function(_, logic, _, _) => logic.function_type(),
        }
    }

    /// Returns the function proving key.
    pub fn proving_key(&self) -> &N::FunctionProvingKey {
        match self {
            Self::Noop => N::noop_circuit_proving_key(),
            Self::Function(_, _, proving_key, _) => &proving_key,
        }
    }

    /// Returns the function verifying key.
    pub fn verifying_key(&self) -> &N::FunctionVerifyingKey {
        match self {
            Self::Noop => N::noop_circuit_verifying_key(),
            Self::Function(_, _, _, verifying_key) => &verifying_key,
        }
    }

    // /// Returns the native evaluation of the function on given records and private variables.
    // pub fn evaluate(
    //     &self,
    //     records: &Vec<Record<N>>,
    //     variables: Arc<dyn PrivateVariables<N>>,
    // ) -> Result<Vec<Record<N>>, ProgramError> {
    //     unimplemented!("The native evaluation of this function is unimplemented")
    // }

    /// Returns the native evaluation of the function on given records and private variables.
    pub fn evaluate(
        &self,
        records: &Vec<Record<N>>,
        variables: PrivateVariables<N>,
    ) -> Result<Vec<Record<N>>, ProgramError> {
        unimplemented!("The native evaluation of this function is unimplemented")
    }

    /// Executes the function, returning an proof.
    pub fn execute(&self, public: PublicVariables<N>) -> Result<N::ProgramProof, ProgramError> {
        let circuit = self.synthesize(public.clone());
        let proof = <N::ProgramSNARK as SNARK>::prove(self.proving_key(), &circuit, &mut thread_rng())?;
        assert!(self.verify(&public, &proof));
        Ok(proof)
    }

    /// Returns true if the execution of the function is valid.
    pub fn verify(&self, public: &PublicVariables<N>, proof: &N::ProgramProof) -> bool {
        <N::ProgramSNARK as SNARK>::verify(self.verifying_key(), public, proof)
            .expect("Failed to verify function execution proof")
    }

    /// Returns the assigned circuit.
    pub(crate) fn synthesize(&self, public: PublicVariables<N>) -> SynthesizedCircuit<N> {
        match self {
            Self::Noop => SynthesizedCircuit::Noop(public),
            Self::Function(_, logic, _, _) => SynthesizedCircuit::Assigned(logic.clone(), public),
        }
    }
}

// TODO (howardwu): TEMPORARY - Guard access to this enum, to prevent abuse of it.
pub enum SynthesizedCircuit<N: Network> {
    Noop(PublicVariables<N>),
    Blank(Arc<dyn FunctionLogic<N>>),
    Assigned(Arc<dyn FunctionLogic<N>>, PublicVariables<N>),
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for SynthesizedCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        match self {
            Self::Noop(public) => {
                let _position = UInt8::alloc_input_vec_le(cs.ns(|| "Alloc position"), &[0u8])?;

                let _transition_id_crh = N::TransactionIDCRHGadget::alloc_constant(
                    &mut cs.ns(|| "Declare the transaction ID CRH scheme"),
                    || Ok(N::transition_id_crh().clone()),
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

use crate::{Function, FunctionType, Network, ProgramError, ProgramExecutable, PublicVariables};
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};

use anyhow::Result;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub enum Executable<N: Network> {
    Noop,
    Circuit(N::ProgramID, Function<N>, MerklePath<N::ProgramFunctionsTreeParameters>),
}

impl<N: Network> ProgramExecutable<N> for Executable<N> {
    fn new(
        program_id: N::ProgramID,
        circuit: Function<N>,
        program_path: MerklePath<N::ProgramFunctionsTreeParameters>,
    ) -> Result<Self, ProgramError> {
        assert!(program_path.verify(&program_id, &circuit.function_id())?);
        Ok(Self::Circuit(program_id, circuit, program_path))
    }

    /// Returns the program ID of the executable.
    fn program_id(&self) -> N::ProgramID {
        match self {
            Self::Noop => *N::noop_program_id(),
            Self::Circuit(program_id, _, _) => *program_id,
        }
    }

    /// Returns the circuit type of the executable.
    fn function_type(&self) -> FunctionType {
        match self {
            Self::Noop => FunctionType::Noop,
            Self::Circuit(_, circuit, _) => circuit.function_type(),
        }
    }

    /// Executes the circuit, returning an proof.
    fn execute(&self, public: PublicVariables<N>) -> Result<Execution<N>, ProgramError> {
        let (circuit, verifying_key, program_path) = match self {
            Self::Noop => (
                &Function::Noop,
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
        assert!(circuit.verify(&public, &proof));

        Ok(Execution {
            program_id: self.program_id(),
            program_path,
            verifying_key,
            proof,
        })
    }
}
