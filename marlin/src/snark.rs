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

//! The Marlin zkSNARK implementation
use crate::{CircuitParameters, Marlin, Proof, UniversalSRS};
use snarkvm_errors::algorithms::SNARKError;
use snarkvm_models::{
    algorithms::SNARK,
    curves::{to_field_vec::ToConstraintField, PairingEngine},
    gadgets::r1cs::ConstraintSynthesizer,
};
use snarkvm_profiler::{end_timer, start_timer};

pub use snarkvm_polycommit::{marlin_pc::MarlinKZG10 as MultiPC, PCCommitment};

use blake2::Blake2s;
use core::marker::PhantomData;
use rand_core::RngCore;

// A structured reference string which will be used to derive a circuit-specific
// common reference string

// Type alias for a Marlin instance using the KZG10 polynomial commitment and Blake2s

/// A circuit-specific proving key.
pub type ProverKey<E> = crate::CircuitProvingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

/// A circuit-specific verification key.
pub type VerifierKey<E> = crate::CircuitVerifyingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

impl<E: PairingEngine> From<CircuitParameters<E>> for VerifierKey<E> {
    fn from(params: CircuitParameters<E>) -> Self {
        params.verifier_key
    }
}

/// The Marlin zkSNARK implementation
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarlinSnark<'a, E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
{
    _engine: PhantomData<E>,
    _circuit: PhantomData<C>,
    _verifier_input: PhantomData<V>,
    _key_lifetime: PhantomData<&'a ProverKey<E>>,
}

impl<'a, E, C, V> SNARK for MarlinSnark<'a, E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
{
    type AssignedCircuit = C;
    type Circuit = (C, UniversalSRS<<E as PairingEngine>::Fr, MultiPC<E>>);
    // Abuse the Circuit type to pass the SRS as well.
    type PreparedVerificationParameters = VerifierKey<E>;
    type Proof = Proof<<E as PairingEngine>::Fr, MultiPC<E>>;
    type ProvingParameters = CircuitParameters<E>;
    type VerificationParameters = VerifierKey<E>;
    type VerifierInput = V;

    fn setup<R: RngCore>(
        (circuit, srs): &Self::Circuit,
        _rng: &mut R, // The Marlin Setup is deterministic
    ) -> Result<(Self::ProvingParameters, Self::PreparedVerificationParameters), SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Setup");
        let parameters = CircuitParameters::<E>::new(circuit, srs)?;
        end_timer!(setup_time);
        let verifier_key = parameters.verifier_key.clone();
        Ok((parameters, verifier_key))
    }

    fn prove<R: RngCore>(
        pp: &Self::ProvingParameters,
        circuit: &Self::AssignedCircuit,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let proving_time = start_timer!(|| "{Marlin}::Proving");
        let proof = Marlin::<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>::prove(&pp.prover_key, circuit, rng)
            .map_err(|_| SNARKError::Crate("marlin", "Could not generate proof".to_owned()))?;
        end_timer!(proving_time);
        Ok(proof)
    }

    fn verify(
        vk: &Self::PreparedVerificationParameters,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verification_time = start_timer!(|| "{Marlin}::Verifying");
        let res = Marlin::<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>::verify(
            &vk,
            &input.to_field_elements()?,
            &proof,
            &mut rand_core::OsRng,
        )
        .map_err(|_| SNARKError::Crate("marlin", "Could not verify proof".to_owned()))?;
        end_timer!(verification_time);

        Ok(res)
    }
}
