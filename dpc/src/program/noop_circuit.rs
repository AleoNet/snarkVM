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

use crate::{CircuitError, Parameters, ProgramCircuit, ProgramPrivateVariables, ProgramPublicVariables};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, ToConstraintField};

use rand::{CryptoRng, Rng};
use std::marker::PhantomData;

pub struct NoopPrivateVariables<C: Parameters>(PhantomData<C>);

impl<C: Parameters> ProgramPrivateVariables<C> for NoopPrivateVariables<C> {}

impl<C: Parameters> NoopPrivateVariables<C> {
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopCircuit<C: Parameters> {
    circuit_id: <C::ProgramCircuitIDCRH as CRH>::Output,
    #[derivative(Debug = "ignore")]
    proving_key: <C::ProgramSNARK as SNARK>::ProvingKey,
    #[derivative(Debug = "ignore")]
    verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey,
}

impl<C: Parameters> ProgramCircuit<C> for NoopCircuit<C> {
    /// Initializes a new instance of the noop circuit.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, CircuitError> {
        let (proving_key, prepared_verifying_key) = <C::ProgramSNARK as SNARK>::setup(
            &NoopAllocatedCircuit::<C>::default(),
            &mut *C::program_srs::<R>(rng).borrow_mut(),
        )?;
        let verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey = prepared_verifying_key.into();

        // Compute the noop circuit ID.
        let circuit_id = <C as Parameters>::program_circuit_id(&verifying_key)?;

        Ok(Self {
            circuit_id,
            proving_key,
            verifying_key,
        })
    }

    /// Loads an instance of the noop circuit.
    fn load() -> Result<Self, CircuitError> {
        let proving_key = C::noop_program_proving_key().clone();
        let verifying_key = C::noop_program_verifying_key().clone();

        // Compute the circuit ID.
        let circuit_id =
            <C as Parameters>::program_circuit_id_crh().hash_field_elements(&verifying_key.to_field_elements()?)?;

        Ok(Self {
            circuit_id,
            proving_key,
            verifying_key,
        })
    }

    /// Returns the circuit ID.
    fn circuit_id(&self) -> &<C::ProgramCircuitIDCRH as CRH>::Output {
        &self.circuit_id
    }

    /// Returns the circuit proving key.
    fn proving_key(&self) -> &<C::ProgramSNARK as SNARK>::ProvingKey {
        &self.proving_key
    }

    /// Returns the circuit verifying key.
    fn verifying_key(&self) -> &<C::ProgramSNARK as SNARK>::VerifyingKey {
        &self.verifying_key
    }

    /// Executes the circuit, returning an proof.
    fn execute(
        &self,
        public: &ProgramPublicVariables<C>,
        _private: &dyn ProgramPrivateVariables<C>,
    ) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError> {
        // Compute the proof.
        let rng = &mut rand::thread_rng();
        let allocated_circuit = NoopAllocatedCircuit::<C> { public: public.clone() };
        let proof = <C::ProgramSNARK as SNARK>::prove(&self.proving_key, &allocated_circuit, rng)?;
        assert!(self.verify(public, &proof));
        Ok(proof)
    }

    /// Executes the circuit, returning an proof.
    fn execute_blank(&self) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError> {
        // Compute the proof.
        let rng = &mut rand::thread_rng();
        let allocated_circuit = NoopAllocatedCircuit::<C>::default();
        let proof = <C::ProgramSNARK as SNARK>::prove(&self.proving_key, &allocated_circuit, rng)?;
        Ok(proof)
    }

    /// Returns true if the execution of the circuit is valid.
    fn verify(&self, public: &ProgramPublicVariables<C>, proof: &<C::ProgramSNARK as SNARK>::Proof) -> bool {
        <C::ProgramSNARK as SNARK>::verify(&self.verifying_key.clone().into(), public, proof)
            .expect("Failed to verify program execution proof")
    }
}

#[derive(Derivative)]
#[derivative(Default(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
struct NoopAllocatedCircuit<C: Parameters> {
    public: ProgramPublicVariables<C>,
}

impl<C: Parameters> ConstraintSynthesizer<C::InnerScalarField> for NoopAllocatedCircuit<C> {
    fn generate_constraints<CS: ConstraintSystem<C::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let _record_position =
            UInt8::alloc_input_vec_le(cs.ns(|| "Alloc record position"), &[self.public.record_position])?;

        let _local_data_commitment_scheme = C::LocalDataCommitmentGadget::alloc_constant(
            &mut cs.ns(|| "Declare the local data commitment scheme"),
            || Ok(C::local_data_commitment_scheme().clone()),
        )?;

        let _local_data_root = <C::LocalDataCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            cs.ns(|| "Alloc local data root"),
            || Ok(self.public.local_data_root),
        )?;

        Ok(())
    }
}
