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

use crate::{CircuitError, ExecutionType, Network, PrivateVariables, ProgramCircuit, PublicVariables};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use rand::{CryptoRng, Rng};
use std::marker::PhantomData;

pub struct NoopPrivateVariables<N: Network>(PhantomData<N>);

impl<N: Network> PrivateVariables<N> for NoopPrivateVariables<N> {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl<N: Network> NoopPrivateVariables<N> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"), Debug(bound = "N: Network"))]
pub struct NoopCircuit<N: Network> {
    circuit_id: N::ProgramCircuitID,
    #[derivative(Debug = "ignore")]
    proving_key: <N::ProgramSNARK as SNARK>::ProvingKey,
    #[derivative(Debug = "ignore")]
    verifying_key: <N::ProgramSNARK as SNARK>::VerifyingKey,
}

impl<N: Network> ProgramCircuit<N> for NoopCircuit<N> {
    /// Initializes a new instance of the noop circuit.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, CircuitError> {
        let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
            &NoopAllocatedCircuit::<N>::default(),
            &mut *N::program_srs::<R>(rng).borrow_mut(),
        )?;

        Ok(Self {
            circuit_id: <N as Network>::program_circuit_id(&verifying_key)?,
            proving_key,
            verifying_key,
        })
    }

    /// Loads an instance of the noop circuit.
    fn load() -> Result<Self, CircuitError> {
        Ok(Self {
            circuit_id: N::noop_circuit_id().clone(),
            proving_key: N::noop_circuit_proving_key().clone(),
            verifying_key: N::noop_circuit_verifying_key().clone(),
        })
    }

    /// Returns the circuit ID.
    fn circuit_id(&self) -> &N::ProgramCircuitID {
        &self.circuit_id
    }

    /// Returns the circuit proving key.
    fn proving_key(&self) -> &<N::ProgramSNARK as SNARK>::ProvingKey {
        &self.proving_key
    }

    /// Returns the circuit verifying key.
    fn verifying_key(&self) -> &<N::ProgramSNARK as SNARK>::VerifyingKey {
        &self.verifying_key
    }

    /// Returns the circuit execution type.
    fn execution_type(&self) -> ExecutionType {
        ExecutionType::Noop
    }

    /// Executes the circuit, returning an proof.
    fn execute(
        &self,
        public: &PublicVariables<N>,
        _private: &dyn PrivateVariables<N>,
    ) -> Result<<N::ProgramSNARK as SNARK>::Proof, CircuitError> {
        // Compute the proof.
        let rng = &mut rand::thread_rng();
        let allocated_circuit = NoopAllocatedCircuit::<N> { public: public.clone() };
        let proof = <N::ProgramSNARK as SNARK>::prove(&self.proving_key, &allocated_circuit, rng)?;
        assert!(self.verify(public, &proof));
        Ok(proof)
    }

    /// Executes the circuit, returning an proof.
    fn execute_blank(&self) -> Result<<N::ProgramSNARK as SNARK>::Proof, CircuitError> {
        // Compute the proof.
        let rng = &mut rand::thread_rng();
        let allocated_circuit = NoopAllocatedCircuit::<N>::default();
        let proof = <N::ProgramSNARK as SNARK>::prove(&self.proving_key, &allocated_circuit, rng)?;
        Ok(proof)
    }

    /// Returns true if the execution of the circuit is valid.
    fn verify(&self, public: &PublicVariables<N>, proof: &<N::ProgramSNARK as SNARK>::Proof) -> bool {
        <N::ProgramSNARK as SNARK>::verify(&self.verifying_key.clone().into(), public, proof)
            .expect("Failed to verify program execution proof")
    }
}

#[derive(Derivative)]
#[derivative(Default(bound = "N: Network"), Debug(bound = "N: Network"))]
struct NoopAllocatedCircuit<N: Network> {
    public: PublicVariables<N>,
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for NoopAllocatedCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let _record_position =
            UInt8::alloc_input_vec_le(cs.ns(|| "Alloc record position"), &[self.public.record_position])?;

        let _local_data_commitment_scheme = N::LocalDataCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare the local data commitment scheme"),
            || Ok(N::local_data_commitment_scheme().clone()),
        )?;

        let _local_data_root = <N::LocalDataCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            cs.ns(|| "Alloc local data root"),
            || Ok(self.public.local_data_root),
        )?;

        Ok(())
    }
}
