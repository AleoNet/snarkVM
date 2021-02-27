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
use crate::{
    marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinSNARK, Proof, UniversalSRS},
    Parameters,
};
use snarkvm_errors::algorithms::SNARKError;
use snarkvm_models::{
    algorithms::SNARK,
    curves::{to_field_vec::ToConstraintField, PairingEngine},
    gadgets::r1cs::ConstraintSynthesizer,
};
use snarkvm_profiler::{end_timer, start_timer};

pub use snarkvm_polycommit::{marlin_pc::MarlinKZG10 as MultiPC, PolynomialCommitment};

use blake2::Blake2s;
use core::marker::PhantomData;
use rand_core::RngCore;

/// A structured reference string which will be used to derive a circuit-specific
/// common reference string
pub type SRS<E> = UniversalSRS<<E as PairingEngine>::Fr, MultiPC<E>>;

/// Type alias for a Marlin instance using the KZG10 polynomial commitment and Blake2s
pub type Marlin<E> = MarlinSystem<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>;

/// A circuit-specific proving key.
pub type ProvingKey<E> = CircuitProvingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

/// A circuit-specific verifying key.
pub type VerifyingKey<E> = CircuitVerifyingKey<<E as PairingEngine>::Fr, MultiPC<E>>;

impl<E: PairingEngine> From<Parameters<E>> for VerifyingKey<E> {
    fn from(parameters: Parameters<E>) -> Self {
        parameters.verifying_key
    }
}

/// A Marlin instance using the KZG10 polynomial commitment and Blake2s
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarlinSystem<E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
{
    _engine: PhantomData<E>,
    _circuit: PhantomData<C>,
    _verifier_input: PhantomData<V>,
}

impl<E, C, V> SNARK for MarlinSystem<E, C, V>
where
    E: PairingEngine,
    C: ConstraintSynthesizer<E::Fr>,
    V: ToConstraintField<E::Fr>,
{
    type AssignedCircuit = C;
    type Circuit = (C, SRS<E>);
    // Abuse the Circuit type to pass the SRS as well.
    type PreparedVerificationParameters = VerifyingKey<E>;
    type Proof = Proof<<E as PairingEngine>::Fr, MultiPC<E>>;
    type ProvingParameters = Parameters<E>;
    type VerificationParameters = VerifyingKey<E>;
    type VerifierInput = V;

    fn setup<R: RngCore>(
        (circuit, srs): &Self::Circuit,
        _rng: &mut R, // The Marlin circuit setup is deterministic.
    ) -> Result<(Self::ProvingParameters, Self::PreparedVerificationParameters), SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Setup");
        let parameters = Parameters::<E>::new(circuit, srs)?;
        end_timer!(setup_time);

        let verifying_key = parameters.verifying_key.clone();
        Ok((parameters, verifying_key))
    }

    fn prove<R: RngCore>(
        parameters: &Self::ProvingParameters,
        circuit: &Self::AssignedCircuit,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let proving_time = start_timer!(|| "{Marlin}::Proving");
        let proof =
            MarlinSNARK::<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>::prove(&parameters.proving_key, circuit, rng)
                .map_err(|_| SNARKError::Crate("marlin", "Could not generate proof".to_owned()))?;
        end_timer!(proving_time);
        Ok(proof)
    }

    fn verify(
        verifying_key: &Self::PreparedVerificationParameters,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verification_time = start_timer!(|| "{Marlin}::Verifying");
        let res = MarlinSNARK::<<E as PairingEngine>::Fr, MultiPC<E>, Blake2s>::verify(
            &verifying_key,
            &input.to_field_elements()?,
            &proof,
            &mut rand_core::OsRng,
        )
        .map_err(|_| SNARKError::Crate("marlin", "Could not verify proof".to_owned()))?;
        end_timer!(verification_time);

        Ok(res)
    }
}
//
// impl<E, C, V> MarlinSystem<E, C, V>
// where
//     E: PairingEngine,
//     C: ConstraintSynthesizer<E::Fr>,
//     V: ToConstraintField<E::Fr>,
// {
//     /// Generates the universal proving and verifying keys for the argument system.
//     pub fn universal_setup<R: RngCore>(
//         num_constraints: usize,
//         num_variables: usize,
//         num_non_zero: usize,
//         rng: &mut R,
//     ) -> Result<SRS<E>, MarlinError<<MultiPC<E> as PolynomialCommitment<E::Fr>>::Error>> {
//         let max_degree = crate::ahp::AHPForR1CS::<E::Fr>::max_degree(num_constraints, num_variables, num_non_zero)?;
//         let setup_time = start_timer!(|| {
//             format!(
//                 "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
//                 max_degree, num_constraints, num_variables, num_non_zero,
//             )
//         });
//
//         let srs = MultiPC::<E>::setup(max_degree, rng).map_err(MarlinError::from_pc_err);
//         end_timer!(setup_time);
//         srs
//     }
// }
