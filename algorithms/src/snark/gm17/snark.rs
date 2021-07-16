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

use super::{
    create_random_proof,
    generate_random_parameters,
    verify_proof,
    PreparedVerifyingKey,
    Proof,
    ProvingKey,
    VerifyingKey,
};
use crate::{errors::SNARKError, traits::SNARK};
use snarkvm_curves::traits::PairingEngine;
use snarkvm_fields::ToConstraintField;
use snarkvm_r1cs::ConstraintSynthesizer;

use rand::Rng;
use std::marker::PhantomData;

/// Note: V should serialize its contents to `Vec<E::Fr>` in the same order as
/// during the constraint generation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GM17<E: PairingEngine, V: ToConstraintField<E::Fr> + ?Sized> {
    _engine: PhantomData<E>,
    _verifier_input: PhantomData<V>,
}

impl<E: PairingEngine, V: ToConstraintField<E::Fr> + ?Sized> SNARK<E::Fr> for GM17<E, V> {
    type PreparedVerifyingKey = PreparedVerifyingKey<E>;
    type Proof = Proof<E>;
    type ProvingKey = ProvingKey<E>;
    type UniversalReferenceString = ();
    type VerifierInput = V;
    type VerifyingKey = VerifyingKey<E>;

    fn setup<C: ConstraintSynthesizer<E::Fr>, R: Rng>(
        circuit: &C,
        _: &Self::UniversalReferenceString,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError> {
        let setup_time = start_timer!(|| "{Groth-Maller 2017}::Setup");
        let pp = generate_random_parameters::<E, C, R>(&circuit, rng)?;
        let vk = pp.vk.clone();
        end_timer!(setup_time);
        Ok((pp, vk))
    }

    fn prove<C: ConstraintSynthesizer<E::Fr>, R: Rng>(
        proving_key: &Self::ProvingKey,
        input_and_witness: &C,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        let proof_time = start_timer!(|| "{Groth-Maller 2017}::Prove");
        let result = create_random_proof::<E, _, _>(input_and_witness, proving_key, rng)?;
        end_timer!(proof_time);
        Ok(result)
    }

    fn verify_with_processed_key(
        processed_verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        let verify_time = start_timer!(|| "{Groth-Maller 2017}::Verify");
        let conversion_time = start_timer!(|| "Convert input to E::Fr");
        let input = input.to_field_elements()?;
        end_timer!(conversion_time);
        let verification = start_timer!(|| format!("Verify proof w/ input len: {}", input.len()));
        let result = verify_proof(&processed_verifying_key, proof, &input)?;
        end_timer!(verification);
        end_timer!(verify_time);
        Ok(result)
    }
}
