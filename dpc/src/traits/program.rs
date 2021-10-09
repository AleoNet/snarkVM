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

use crate::{FunctionType, Network, ProgramError, PublicVariables, Request, Response};
use snarkvm_algorithms::merkle_tree::MerklePath;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use anyhow::Result;
use std::sync::Arc;

pub trait ProgramScheme<N: Network> {
    /// Initializes an instance of the program with the given functions.
    fn new(functions: Vec<Arc<dyn Function<N>>>) -> Result<Self>
    where
        Self: Sized;

    /// Initializes an instance of the noop program.
    fn new_noop() -> Result<Self>
    where
        Self: Sized;

    /// Returns the program ID.
    fn program_id(&self) -> N::ProgramID;

    /// Returns `true` if the given function ID exists in the program.
    fn contains_function(&self, function_id: &N::FunctionID) -> bool;

    /// Returns the function given the function ID, if it exists.
    fn to_function(&self, function_id: &N::FunctionID) -> Result<Arc<dyn Function<N>>>;

    /// Returns the program path (the Merkle path for a given function ID).
    fn to_program_path(&self, function_id: &N::FunctionID) -> Result<MerklePath<N::ProgramFunctionsTreeParameters>>;

    /// Performs a native evaluation of the function for a given request.
    fn evaluate(&self, request: &Request<N>) -> Result<Response<N>>;
}

pub trait Function<N: Network>: Send + Sync {
    /// Returns the function ID.
    fn function_id(&self) -> N::FunctionID;

    /// Returns the circuit type.
    fn function_type(&self) -> FunctionType;

    /// Performs a native evaluation of the function for a given request.
    fn evaluate(&self, request: &Request<N>) -> Result<Response<N>, ProgramError>;

    /// Executes the function, returning an proof.
    fn execute(&self, public: PublicVariables<N>) -> Result<N::ProgramProof, ProgramError>;

    /// Returns true if the execution of the function is valid.
    fn verify(&self, public: &PublicVariables<N>, proof: &N::ProgramProof) -> bool;

    // /// Synthesizes the circuit inside the given constraint system.
    // fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
    //     &self,
    //     cs: &mut CS,
    //     public: &PublicVariables<N>,
    // ) -> Result<(), SynthesisError>
    // where
    //     Self: Sized;
}

// pub trait PrivateVariables<N: Network>:
//     ToConstraintField<N::InnerScalarField> + Debug + ToBytes + FromBytes + Send + Sync
// {
//     /// Initializes a blank instance of the private variables, typically used for a SNARK setup.
//     fn new_blank() -> Result<Self>
//     where
//         Self: Sized;
//
//     fn as_any(&self) -> &dyn std::any::Any;
// }

// use snarkvm_fields::ConstraintFieldError;

// use std::io::{Read, Result as IoResult, Write};

use snarkvm_algorithms::SNARK;
use snarkvm_gadgets::prelude::*;
use snarkvm_r1cs::ConstraintSynthesizer;

use std::marker::PhantomData;

pub struct Noop<N: Network>(PhantomData<N>);

impl<N: Network> Noop<N> {
    /// Returns the noop function.
    pub fn new() -> Self {
        Self(PhantomData)
    }
}

impl<N: Network> Function<N> for Noop<N> {
    /// Returns the function ID.
    fn function_id(&self) -> N::FunctionID {
        *N::noop_circuit_id()
    }

    /// Returns the circuit type.
    fn function_type(&self) -> FunctionType {
        FunctionType::Noop
    }

    /// Performs a native evaluation of the function for a given request.
    fn evaluate(&self, _request: &Request<N>) -> Result<Response<N>, ProgramError> {
        Ok(Response::new_noop(&mut rand::thread_rng())?)
    }

    /// Executes the function, returning an proof.
    fn execute(&self, public: PublicVariables<N>) -> Result<N::ProgramProof, ProgramError> {
        let circuit = SynthesizedCircuit::Noop(public.clone());
        let proof =
            <N::ProgramSNARK as SNARK>::prove(N::noop_circuit_proving_key(), &circuit, &mut rand::thread_rng())?;
        assert!(self.verify(&public, &proof));
        Ok(proof)
    }

    /// Returns true if the execution of the function is valid.
    fn verify(&self, public: &PublicVariables<N>, proof: &N::ProgramProof) -> bool {
        <N::ProgramSNARK as SNARK>::verify(N::noop_circuit_verifying_key(), public, proof)
            .expect("Failed to verify noop function proof")
    }
}

// TODO (howardwu): TEMPORARY - Guard access to this enum, to prevent abuse of it.
pub enum SynthesizedCircuit<N: Network> {
    Noop(PublicVariables<N>),
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
                    &mut cs.ns(|| "Declare the transaction ID CRH scheme"),
                    || Ok(N::transition_id_crh().clone()),
                )?;

                let _transaction_id = <N::TransitionIDCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
                    cs.ns(|| "Alloc the transaction ID"),
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
// #[derive(Clone, Debug)]
// pub struct NoopVariables<N: Network>(PhantomData<N>);
// impl<N: Network> PrivateVariables<N> for NoopVariables<N> {
//     fn new_blank() -> Result<Self> {
//         Ok(Self(PhantomData))
//     }
//
//     fn as_any(&self) -> &dyn std::any::Any {
//         self
//     }
// }
//
// impl<N: Network> FromBytes for NoopVariables<N> {
//     #[inline]
//     fn read_le<R: Read>(_reader: R) -> IoResult<Self> {
//         Ok(Self(PhantomData))
//     }
// }
//
// impl<N: Network> ToBytes for NoopVariables<N> {
//     fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
//         Ok(())
//     }
// }
//
// // impl<N: Network> From<NoopVariables<N>> for Arc<NoopVariables<N>> {
// //     fn from(variables: NoopVariables<N>) -> Arc<NoopVariables<N>> {
// //         Arc::new(variables)
// //     }
// // }
//
// impl<N: Network> ToConstraintField<N::InnerScalarField> for NoopVariables<N> {
//     #[inline]
//     fn to_field_elements(&self) -> Result<Vec<N::InnerScalarField>, ConstraintFieldError> {
//         Ok(Vec::new())
//     }
// }
