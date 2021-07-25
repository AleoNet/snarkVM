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
    constraints::snark::MarlinBound,
    fiat_shamir::FiatShamirChaChaRng,
    marlin::{
        CircuitProvingKey,
        CircuitVerifyingKey,
        MarlinSNARK,
        MarlinTestnet1Mode,
        PreparedCircuitVerifyingKey,
        Proof,
        UniversalSRS,
    },
    Parameters,
};
use snarkvm_algorithms::{SNARKError, SNARK, SRS};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::ToConstraintField;
use snarkvm_profiler::{end_timer, start_timer};
use snarkvm_r1cs::ConstraintSynthesizer;
use snarkvm_utilities::FromBytes;

pub use snarkvm_polycommit::{marlin_pc::MarlinKZG10 as MultiPC, PolynomialCommitment};

use blake2::Blake2s;
use core::marker::PhantomData;
use rand::{CryptoRng, Rng};

/// A structured reference string which will be used to derive a circuit-specific
/// common reference string
pub type URS<E> = UniversalSRS<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, MultiPC<E>>;

/// A circuit-specific proving key.
pub type ProvingKey<E> = CircuitProvingKey<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, MultiPC<E>>;

/// A circuit-specific verifying key.
pub type VerifyingKey<E> = CircuitVerifyingKey<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, MultiPC<E>>;

impl<E: PairingEngine> From<Parameters<E>> for VerifyingKey<E> {
    fn from(parameters: Parameters<E>) -> Self {
        parameters.verifying_key
    }
}

/// A prepared circuit-specific verifying key.
pub type PreparedVerifyingKey<E> =
    PreparedCircuitVerifyingKey<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, MultiPC<E>>;

/// The Marlin proof system for testnet1.
pub type MarlinTestnet1<E> = MarlinSNARK<
    <E as PairingEngine>::Fr,
    <E as PairingEngine>::Fq,
    MultiPC<E>,
    FiatShamirChaChaRng<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, Blake2s>,
    MarlinTestnet1Mode,
>;

/// A Marlin instance using the KZG10 polynomial commitment and Blake2s
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarlinTestnet1System<E, V>
where
    E: PairingEngine,
    V: ToConstraintField<E::Fr>,
{
    _engine: PhantomData<E>,
    _verifier_input: PhantomData<V>,
}

impl<E, V> SNARK for MarlinTestnet1System<E, V>
where
    E: PairingEngine,
    V: ToConstraintField<E::Fr>,
{
    type BaseField = E::Fq;
    type PreparedVerifyingKey = PreparedVerifyingKey<E>;
    type Proof = Proof<<E as PairingEngine>::Fr, <E as PairingEngine>::Fq, MultiPC<E>>;
    type ProvingKey = Parameters<E>;
    type ScalarField = E::Fr;
    type UniversalSetupConfig = MarlinBound;
    type UniversalSetupParameters = URS<E>;
    type VerifierInput = V;
    type VerifyingKey = VerifyingKey<E>;

    fn universal_setup<R: Rng + CryptoRng>(
        config: &Self::UniversalSetupConfig,
        rng: &mut R,
    ) -> Result<Self::UniversalSetupParameters, SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Setup");
        let srs = MarlinTestnet1::<E>::universal_setup(config.max_degree, rng)?;
        end_timer!(setup_time);
        Ok(srs)
    }

    fn setup<C: ConstraintSynthesizer<E::Fr>>(
        circuit: &C,
        srs: &mut SRS<impl Rng + CryptoRng>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Index");
        let (pk, vk) = match srs {
            SRS::CircuitSpecific(rng) => {
                let (pk, vk) = MarlinTestnet1::<E>::circuit_specific_setup(circuit, rng)?;
                (
                    Parameters::<E> {
                        proving_key: pk,
                        verifying_key: vk.clone(),
                    },
                    vk,
                )
            }
            SRS::Universal(srs) => {
                let srs: Self::UniversalSetupParameters = FromBytes::from_bytes_le(srs)?;
                let parameters = Parameters::<E>::new(circuit, &srs)?;
                let verifying_key = parameters.verifying_key.clone();
                (parameters, verifying_key)
            }
        };
        end_timer!(setup_time);
        Ok((pk, vk))
    }

    fn prove<C: ConstraintSynthesizer<E::Fr>, R: Rng + CryptoRng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let proving_time = start_timer!(|| "{Marlin}::Proving");
        let proof = MarlinTestnet1::<E>::prove(&proving_key.proving_key, input_and_witness, rng)
            .map_err(|error| SNARKError::Crate("marlin", format!("Failed to generate proof - {:?}", error)))?;
        end_timer!(proving_time);
        Ok(proof)
    }

    fn verify(
        verifying_key: &Self::VerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verification_time = start_timer!(|| "{Marlin}::Verifying");
        let res = MarlinTestnet1::<E>::verify(&verifying_key, &input.to_field_elements()?, &proof)
            .map_err(|_| SNARKError::Crate("marlin", "Could not verify proof".to_owned()))?;
        end_timer!(verification_time);

        Ok(res)
    }

    fn verify_prepared(
        verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verification_time = start_timer!(|| "{Marlin}::PreparedVerifying");
        let res = MarlinTestnet1::<E>::prepared_verify(&verifying_key, &input.to_field_elements()?, &proof)
            .map_err(|_| SNARKError::Crate("marlin", "Could not verify proof".to_owned()))?;
        end_timer!(verification_time);

        Ok(res)
    }
}
