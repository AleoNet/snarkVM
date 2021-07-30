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

use crate::{CircuitError, Parameters, ProgramCircuit, ProgramExecutable, ProgramPublicVariables};
use snarkvm_algorithms::prelude::*;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, ToConstraintField};
use snarkvm_utilities::ToBytes;

use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"), Debug(bound = "C: Parameters"))]
pub struct NoopCircuit<C: Parameters> {
    #[derivative(Default(value = "vec![0u8; 48]"))]
    circuit_id: Vec<u8>,
    #[derivative(Debug = "ignore")]
    proving_key: <C::ProgramSNARK as SNARK>::ProvingKey,
    #[derivative(Debug = "ignore")]
    verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey,
}

impl<C: Parameters> ProgramCircuit<C> for NoopCircuit<C> {
    /// Initializes a new instance of the noop circuit.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, CircuitError> {
        let (proving_key, prepared_verifying_key) =
            <C::ProgramSNARK as SNARK>::setup(&NoopAllocatedCircuit::<C>::default(), &mut C::program_srs::<R>(rng)?)?;
        let verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey = prepared_verifying_key.into();

        // Compute the noop circuit ID.
        let circuit_id = <C as Parameters>::program_id_crh()
            .hash_field_elements(&verifying_key.to_field_elements()?)?
            .to_bytes_le()?;

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
        let circuit_id = <C as Parameters>::program_id_crh()
            .hash_field_elements(&verifying_key.to_field_elements()?)?
            .to_bytes_le()?;

        Ok(Self {
            circuit_id,
            proving_key,
            verifying_key,
        })
    }

    /// Returns the circuit ID.
    fn circuit_id(&self) -> &Vec<u8> {
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
}

impl<C: Parameters> ProgramExecutable<C> for NoopCircuit<C> {
    type PrivateVariables = ();

    /// Executes the circuit, returning an execution.
    fn execute<R: Rng + CryptoRng>(
        &self,
        public: &ProgramPublicVariables<C>,
        _private: &Self::PrivateVariables,
        rng: &mut R,
    ) -> Result<<C::ProgramSNARK as SNARK>::Proof, CircuitError> {
        // Compute the proof.
        let allocated_circuit = NoopAllocatedCircuit::<C> { public: public.clone() };
        let proof = <C::ProgramSNARK as SNARK>::prove(&self.proving_key, &allocated_circuit, rng)?;

        Ok(proof)
    }

    /// Returns true if the execution of the circuit is valid.
    fn verify<R: Rng + CryptoRng>(
        &self,
        public: &ProgramPublicVariables<C>,
        proof: <C::ProgramSNARK as SNARK>::Proof,
    ) -> bool {
        <C::ProgramSNARK as SNARK>::verify(&self.verifying_key.clone().into(), &public, &proof)
            .expect("Failed to verify program execution proof")
    }
}

impl<C: Parameters> NoopCircuit<C> {
    #[deprecated]
    pub fn to_snark_parameters(
        &self,
    ) -> (
        <C::ProgramSNARK as SNARK>::ProvingKey,
        <C::ProgramSNARK as SNARK>::VerifyingKey,
    ) {
        (self.proving_key.clone(), self.verifying_key.clone())
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
