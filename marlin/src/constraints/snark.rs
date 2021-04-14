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

use crate::{
    constraints::{
        error::MarlinConstraintsError,
        proof::ProofVar,
        verifier::MarlinVerificationGadget,
        verifier_key::{CircuitVerifyingKeyVar, PreparedCircuitVerifyingKeyVar},
        UniversalSRS,
    },
    fiat_shamir::FiatShamirRng,
    marlin::{
        CircuitProvingKey,
        CircuitVerifyingKey,
        MarlinError,
        MarlinMode,
        MarlinSNARK as MarlinCore,
        PreparedCircuitVerifyingKey,
        Proof,
    },
    FiatShamirRngVar,
};

use snarkvm_algorithms::{SNARKError, SNARK};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::{algorithms::SNARKGadget, fields::ToConstraintFieldGadget},
    utilities::boolean::Boolean,
};
use snarkvm_nonnative::NonNativeFieldInputVar;
use snarkvm_polycommit::{PCCheckVar, PolynomialCommitment};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

use rand::{CryptoRng, Rng, RngCore};
use std::{
    fmt::{Debug, Formatter},
    marker::PhantomData,
};

/// Marlin bound.
#[derive(Clone, PartialEq, PartialOrd)]
pub struct MarlinBound {
    /// Maximum degree for universal setup.
    pub max_degree: usize,
}

impl Default for MarlinBound {
    fn default() -> Self {
        Self { max_degree: 200000 }
    }
}

impl Debug for MarlinBound {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.max_degree)
    }
}

/// The Marlin proof system.
pub struct MarlinSNARK<
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F>,
    FS: FiatShamirRng<F, FSF>,
    MC: MarlinMode,
    C: ConstraintSynthesizer<F>,
> {
    f_phantom: PhantomData<F>,
    fsf_phantom: PhantomData<FSF>,
    pc_phantom: PhantomData<PC>,
    fs_phantom: PhantomData<FS>,
    mc_phantom: PhantomData<MC>,
    c_phantom: PhantomData<C>,
}

impl<TargetField, BaseField, PC, FS, MM, C> MarlinSNARK<TargetField, BaseField, PC, FS, MM, C>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    /// Generates the universal proving and verifying keys for the argument system.
    pub fn universal_setup<R: Rng>(
        bound: &MarlinBound,
        rng: &mut R,
    ) -> Result<(MarlinBound, UniversalSRS<TargetField, PC>), Box<MarlinConstraintsError>> {
        let MarlinBound { max_degree } = bound;

        match MarlinCore::<TargetField, BaseField, PC, FS, MM>::universal_setup(1, 1, (max_degree + 5) / 3, rng) {
            Ok(res) => Ok((bound.clone(), res)),
            Err(e) => Err(Box::new(MarlinConstraintsError::from(e))),
        }
    }

    /// Generates the circuit proving and verifying keys.
    /// This is a deterministic algorithm that anyone can rerun.
    #[allow(clippy::type_complexity)]
    pub fn index<R: RngCore>(
        crs: &(MarlinBound, UniversalSRS<TargetField, PC>),
        circuit: C,
        _rng: &mut R,
    ) -> Result<
        (
            <Self as SNARK>::ProvingParameters,
            <Self as SNARK>::VerificationParameters,
        ),
        Box<MarlinConstraintsError>,
    > {
        let index_res = MarlinCore::<TargetField, BaseField, PC, FS, MM>::circuit_setup(&crs.1, &circuit);
        match index_res {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e).into())),
        }
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a trusted setup.
    pub fn circuit_specific_setup<R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(CircuitProvingKey<TargetField, PC>, CircuitVerifyingKey<TargetField, PC>), Box<MarlinConstraintsError>>
    {
        Ok(MarlinCore::<TargetField, BaseField, PC, FS, MM>::circuit_specific_setup(&circuit, rng).unwrap())
    }

    /// Prepare the verifying key.
    pub fn process_vk(
        vk: &CircuitVerifyingKey<TargetField, PC>,
    ) -> Result<PreparedCircuitVerifyingKey<TargetField, PC>, Box<MarlinConstraintsError>> {
        Ok(PreparedCircuitVerifyingKey::prepare(vk))
    }

    /// Verify the proof with the prepared verifying key.
    pub fn verify_with_processed_vk(
        pvk: &PreparedCircuitVerifyingKey<TargetField, PC>,
        x: &[TargetField],
        proof: &Proof<TargetField, PC>,
    ) -> Result<bool, Box<MarlinConstraintsError>> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MM>::prepared_verify(pvk, x, proof) {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e).into())),
        }
    }
}

impl<TargetField, BaseField, PC, FS, MM, C> SNARK for MarlinSNARK<TargetField, BaseField, PC, FS, MM, C>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    type AssignedCircuit = C;
    type Circuit = (C, UniversalSRS<TargetField, PC>);
    type PreparedVerificationParameters = PreparedCircuitVerifyingKey<TargetField, PC>;
    type Proof = Proof<TargetField, PC>;
    type ProvingParameters = CircuitProvingKey<TargetField, PC>;
    type VerificationParameters = CircuitVerifyingKey<TargetField, PC>;
    type VerifierInput = &'static [TargetField];

    fn setup<R: RngCore>(
        (circuit, _srs): &Self::Circuit,
        rng: &mut R, // The Marlin circuit setup is deterministic.
    ) -> Result<(Self::ProvingParameters, Self::PreparedVerificationParameters), SNARKError> {
        let (circuit_proving_key, circuit_verifier_key) =
            MarlinCore::<TargetField, BaseField, PC, FS, MM>::circuit_specific_setup(circuit, rng).unwrap();

        Ok((circuit_proving_key, circuit_verifier_key.into()))
    }

    fn prove<R: Rng>(
        parameters: &Self::ProvingParameters,
        circuit: &Self::AssignedCircuit,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MM>::prove(&parameters, circuit, rng) {
            Ok(res) => Ok(res),
            Err(e) => Err(SNARKError::from(e)),
        }
    }

    fn verify(
        verifying_key: &Self::PreparedVerificationParameters,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MM>::prepared_verify(verifying_key, input, proof) {
            Ok(res) => Ok(res),
            Err(e) => Err(SNARKError::from(e)),
        }
    }
}

/// The Marlin proof system gadget.
pub struct MarlinSNARKGadget<F, FSF, PC, FS, MM, PCG, FSG>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F>,
    FS: FiatShamirRng<F, FSF>,
    MM: MarlinMode,
    PCG: PCCheckVar<F, PC, FSF>,
    FSG: FiatShamirRngVar<F, FSF, FS>,
{
    f_phantom: PhantomData<F>,
    fsf_phantom: PhantomData<FSF>,
    pc_phantom: PhantomData<PC>,
    fs_phantom: PhantomData<FS>,
    mm_phantom: PhantomData<MM>,
    pcg_phantom: PhantomData<PCG>,
    fsg_phantom: PhantomData<FSG>,
}

impl<TargetField, BaseField, PC, FS, MM, PCG, FSG, C>
    SNARKGadget<TargetField, BaseField, MarlinSNARK<TargetField, BaseField, PC, FS, MM, C>>
    for MarlinSNARKGadget<TargetField, BaseField, PC, FS, MM, PCG, FSG>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    FSG: FiatShamirRngVar<TargetField, BaseField, FS>,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    type InputVar = NonNativeFieldInputVar<TargetField, BaseField>;
    type PreparedVerifyingKeyVar = PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, FS, FSG>;
    type ProofVar = ProofVar<TargetField, BaseField, PC, PCG>;
    type VerifierSize = usize;
    type VerifyingKeyVar = CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>;

    fn verifier_size(
        circuit_vk: &<MarlinSNARK<TargetField, BaseField, PC, FS, MM, C> as SNARK>::VerificationParameters,
    ) -> Self::VerifierSize {
        circuit_vk.circuit_info.num_variables
    }

    fn verify_with_processed_vk<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        circuit_pvk: &Self::PreparedVerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError> {
        Ok(
            MarlinVerificationGadget::<TargetField, BaseField, PC, PCG>::prepared_verify(
                cs.ns(|| "prepared_verify"),
                &circuit_pvk,
                &x.val,
                proof,
            )
            .unwrap(),
        )
    }

    fn verify<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        circuit_vk: &Self::VerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError> {
        Ok(
            MarlinVerificationGadget::<TargetField, BaseField, PC, PCG>::verify::<_, FS, FSG>(
                cs.ns(|| "verify"),
                circuit_vk,
                &x.val,
                proof,
            )
            .unwrap(),
        )
    }
}
