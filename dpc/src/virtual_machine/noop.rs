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

use crate::{Function, Network, ProgramPrivateVariables, ProgramPublicVariables};
use snarkvm_algorithms::{MerkleParameters, CRH, SNARK};
use snarkvm_fields::ConstraintFieldError;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, ToConstraintField};
use snarkvm_utilities::{FromBytes, ToBytes, ToMinimalBits};

use anyhow::Result;
use std::{
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
};

pub struct Noop<N: Network> {
    proving_key: <N::ProgramSNARK as SNARK>::ProvingKey,
    verifying_key: <N::ProgramSNARK as SNARK>::VerifyingKey,
}

impl<N: Network> Noop<N> {
    /// Returns the noop function.
    pub fn new(
        proving_key: <N::ProgramSNARK as SNARK>::ProvingKey,
        verifying_key: <N::ProgramSNARK as SNARK>::VerifyingKey,
    ) -> Self {
        Self { proving_key, verifying_key }
    }

    pub fn setup() -> Result<Self> {
        let (proving_key, verifying_key) = <N::ProgramSNARK as SNARK>::setup(
            &SynthesizedCircuit::<N>::Noop(Default::default()),
            &mut *N::program_srs(&mut rand::thread_rng()).borrow_mut(),
        )?;

        Ok(Self { proving_key, verifying_key })
    }
}

impl<N: Network> Function<N> for Noop<N> {
    /// Returns the function ID.
    fn function_id(&self) -> N::FunctionID {
        N::function_id_crh().hash_bits(&self.verifying_key.to_minimal_bits()).unwrap().into()
    }

    /// Synthesizes the circuit inside the given constraint system.
    fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        public: &ProgramPublicVariables<N>,
    ) -> Result<(), SynthesisError> {
        SynthesizedCircuit::Noop(*public).generate_constraints(cs)?;
        Ok(())
    }

    /// Executes the function, returning an proof.
    fn execute(
        &self,
        public: ProgramPublicVariables<N>,
        _private: &dyn ProgramPrivateVariables<N>,
    ) -> Result<N::ProgramProof> {
        let proof = <N::ProgramSNARK as SNARK>::prove(
            &self.proving_key,
            &SynthesizedCircuit::Noop(public),
            &mut rand::thread_rng(),
        )?
        .into();
        assert!(self.verify(&public, &proof));
        Ok(proof)
    }

    /// Returns true if the execution of the function is valid.
    fn verify(&self, public: &ProgramPublicVariables<N>, proof: &N::ProgramProof) -> bool {
        <N::ProgramSNARK as SNARK>::verify(&self.verifying_key, public, proof)
            .expect("Failed to verify noop function proof")
    }
}

// TODO (howardwu): TEMPORARY - Guard access to this enum, to prevent abuse of it.
pub enum SynthesizedCircuit<N: Network> {
    Noop(ProgramPublicVariables<N>),
    // Blank(Arc<dyn FunctionLogic<N>>),
    // Assigned(Arc<dyn FunctionLogic<N>>, PublicVariables<N>),
}

impl<N: Network> ConstraintSynthesizer<N::InnerScalarField> for SynthesizedCircuit<N> {
    fn generate_constraints<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        match self {
            Self::Noop(public) => {
                let _position = UInt8::alloc_input_vec_le(cs.ns(|| "Alloc position"), &[0u8])?;

                let _transition_id_crh = N::TransitionIDCRHGadget::alloc_constant(
                    &mut cs.ns(|| "Declare the transition ID CRH scheme"),
                    || Ok(N::transition_id_parameters().crh()),
                )?;

                let _transition_id = <N::TransitionIDCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
                    cs.ns(|| "Alloc the transition ID"),
                    || Ok(public.transition_id),
                )?;

                Ok(())
            } // Self::Blank(logic) => {
              //     let synthesizer = Self::Assigned(logic.clone(), Default::default());
              //     synthesizer.generate_constraints(cs)
              // }
              // Self::Assigned(_logic, _public) => {
              //     // TODO (howardwu): Add any DPC related safety checks around program executions.
              //     unimplemented!()
              //     // logic.synthesize::<CS>(cs, public)
              // }
        }
    }
}

//
#[derive(Clone, Debug)]
pub struct NoopPrivateVariables<N: Network>(PhantomData<N>);
impl<N: Network> ProgramPrivateVariables<N> for NoopPrivateVariables<N> {
    fn new_blank() -> Result<Self> {
        Ok(Self(PhantomData))
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}

impl<N: Network> FromBytes for NoopPrivateVariables<N> {
    #[inline]
    fn read_le<R: Read>(_reader: R) -> IoResult<Self> {
        Ok(Self(PhantomData))
    }
}

impl<N: Network> ToBytes for NoopPrivateVariables<N> {
    fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
        Ok(())
    }
}

// impl<N: Network> From<NoopVariables<N>> for Arc<NoopVariables<N>> {
//     fn from(variables: NoopVariables<N>) -> Arc<NoopVariables<N>> {
//         Arc::new(variables)
//     }
// }

impl<N: Network> ToConstraintField<N::InnerScalarField> for NoopPrivateVariables<N> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
        Ok(Vec::new())
    }
}
