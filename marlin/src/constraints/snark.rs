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
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, LinearCombination, SynthesisError, Variable};

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

    fn partial_verify<'a>(
        verifying_key: &PreparedCircuitVerifyingKey<TargetField, PC>,
        input: &[TargetField],
        proof: &Proof<TargetField, PC>,
    ) -> Result<
        (
            Vec<snarkvm_polycommit::LinearCombination<TargetField>>,
            Vec<TargetField>,
            Vec<snarkvm_polycommit::LabeledCommitment<PC::Commitment>>,
            snarkvm_polycommit::QuerySet<'a, TargetField>,
            snarkvm_polycommit::Evaluations<'a, TargetField>,
            FS,
        ),
        SNARKError,
    > {
        match MarlinCore::<TargetField, BaseField, PC, FS, MM>::partial_verify(verifying_key, input, proof) {
            Ok(res) => Ok(res),
            Err(e) => Err(SNARKError::from(e)),
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
    type VerifierInput = [TargetField];

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

impl<TargetField, BaseField, PC, FS, MM, PCG, FSG> MarlinSNARKGadget<TargetField, BaseField, PC, FS, MM, PCG, FSG>
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
{
    fn partial_verify<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        verifying_key_orig: &CircuitVerifyingKey<TargetField, PC>,
        circuit_vk: &CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>,
        x: &NonNativeFieldInputVar<TargetField, BaseField>,
        proof: &ProofVar<TargetField, BaseField, PC, PCG>,
    ) -> Result<
        (
            Vec<snarkvm_polycommit::LinearCombinationVar<TargetField, BaseField>>,
            Vec<snarkvm_nonnative::NonNativeFieldVar<TargetField, BaseField>>,
            Vec<Vec<Boolean>>,
            Vec<PCG::PreparedLabeledCommitmentVar>,
            snarkvm_polycommit::QuerySetVar<TargetField, BaseField>,
            snarkvm_polycommit::EvaluationsVar<TargetField, BaseField>,
        ),
        SynthesisError,
    > {
        Ok(
            MarlinVerificationGadget::<TargetField, BaseField, PC, PCG>::partial_verify::<_, FS, FSG>(
                cs.ns(|| "partial_verify"),
                verifying_key_orig,
                circuit_vk,
                &x.val,
                proof,
            )
            .unwrap(),
        )
    }
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

/// Circuit representing the `MarlinBound`
#[derive(Clone)]
pub struct MarlinBoundCircuit<F: PrimeField> {
    /// The Marlin bound.
    pub bound: MarlinBound,
    _fsf_phantom: PhantomData<F>,
}

impl<F: PrimeField> From<MarlinBound> for MarlinBoundCircuit<F> {
    fn from(bound: MarlinBound) -> Self {
        Self {
            bound,
            _fsf_phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for MarlinBoundCircuit<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let MarlinBound { max_degree } = self.bound;

        let num_variables = max_degree / 3;
        let num_constraints = max_degree / 3;

        let mut vars: Vec<Variable> = vec![];
        for i in 0..num_variables - 1 {
            let var_i = cs.alloc(|| format!("var_i_{}", i), || Ok(F::zero()))?;
            vars.push(var_i);
        }

        let mut rng = snarkvm_utilities::test_rng();

        let mut non_zero_remaining = (max_degree + 5) / 3;
        for i in 0..num_constraints {
            if non_zero_remaining > 0 {
                let num_for_this_constraint = std::cmp::min(non_zero_remaining, num_variables - 1);

                let mut lc_a = LinearCombination::zero();
                let mut lc_b = LinearCombination::zero();
                let mut lc_c = LinearCombination::zero();

                for var in vars.iter().take(num_for_this_constraint) {
                    lc_a += (F::rand(&mut rng), *var);
                    lc_b += (F::rand(&mut rng), *var);
                    lc_c += (F::rand(&mut rng), *var);
                }

                cs.enforce(|| format!("enforce_constraint_{}", i), |_| lc_a, |_| lc_b, |_| lc_c);

                non_zero_remaining -= num_for_this_constraint;
            } else {
                cs.enforce(|| format!("enforce_constraint_{}", i), |lc| lc, |lc| lc, |lc| lc);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::{
        constraints::{
            proof::ProverMessageVar,
            snark::{MarlinSNARK, MarlinSNARKGadget},
        },
        fiat_shamir::{
            FiatShamirAlgebraicSpongeRng,
            FiatShamirAlgebraicSpongeRngVar,
            PoseidonSponge,
            PoseidonSpongeVar,
        },
        marlin::MarlinRecursiveMode,
    };
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq, Fr},
        bw6_761::BW6_761,
    };
    use snarkvm_fields::Field;
    use snarkvm_gadgets::{
        curves::bls12_377::PairingGadget as Bls12_377PairingGadget,
        traits::fields::FieldGadget,
        utilities::{alloc::AllocGadget, eq::EqGadget},
    };
    use snarkvm_nonnative::NonNativeFieldVar;
    use snarkvm_polycommit::{
        marlin_pc::{
            commitment::{
                commitment::CommitmentVar,
                labeled_commitment::LabeledCommitmentVar,
                prepared_commitment::PreparedCommitmentVar,
            },
            marlin_kzg10::MarlinKZG10Gadget,
            proof::batch_lc_proof::BatchLCProofVar,
            MarlinKZG10,
        },
        LinearCombinationCoeffVar,
        LinearCombinationVar,
        PrepareGadget,
    };
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::{test_rng, UniformRand};
    // use snarkvm_polycommit::{LinearCombinationCoeffVar, LinearCombinationVar};

    use core::ops::MulAssign;
    use std::collections::HashMap;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_variables: usize,
    }

    impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
        fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.alloc_input(
                || "c",
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    a.mul_assign(&b);
                    Ok(a)
                },
            )?;

            for i in 0..(self.num_variables - 3) {
                let _ = cs.alloc(
                    || format!("var {}", i),
                    || self.a.ok_or(SynthesisError::AssignmentMissing),
                )?;
            }

            for i in 0..(self.num_constraints - 1) {
                cs.enforce(|| format!("constraint {}", i), |lc| lc + a, |lc| lc + b, |lc| lc + c);
            }

            Ok(())
        }
    }

    type PC = MarlinKZG10<Bls12_377>;
    type PCGadget = MarlinKZG10Gadget<Bls12_377, BW6_761, Bls12_377PairingGadget>;

    type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>;
    type FSG = FiatShamirAlgebraicSpongeRngVar<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>;

    type TestSNARK = MarlinSNARK<Fr, Fq, PC, FS, MarlinRecursiveMode, Circuit<Fr>>;
    type TestSNARKGadget = MarlinSNARKGadget<Fr, Fq, PC, FS, MarlinRecursiveMode, PCGadget, FSG>;

    //
    //
    // type TestSNARK = MarlinSNARK<MNT4Fr, MNT4Fq, MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>>, FS4, TestMarlinConfig>;
    // type FS4 = FiatShamirAlgebraicSpongeRng<MNT4Fr, MNT4Fq, PoseidonSponge<MNT4Fq>>;
    // type PCGadget4 = MarlinKZG10Gadget<Mnt64298cycle, DensePolynomial<MNT4Fr>, MNT4PairingVar>;
    // type FSG4 = FiatShamirAlgebraicSpongeRngVar<MNT4Fr, MNT4Fq, PoseidonSponge<MNT4Fq>, PoseidonSpongeVar<MNT4Fq>>;
    // type TestSNARKGadget = MarlinSNARKGadget<
    //     MNT4Fr,
    //     MNT4Fq,
    //     MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>>,
    //     FS4,
    //     TestMarlinConfig,
    //     PCGadget4,
    //     FSG4,
    // >;
    //
    //
    #[test]
    fn marlin_snark_test() {
        let mut rng = test_rng();

        // Construct the circuit.

        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let mut c = a;
        c.mul_assign(&b);

        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints: 100,
            num_variables: 25,
        };

        // Generate the circuit parameters.

        let (pk, vk) = TestSNARK::circuit_specific_setup(circ, &mut rng).unwrap();

        // Test native proof and verification.

        let proof = TestSNARK::prove(&pk, &circ, &mut rng).unwrap();

        assert!(
            TestSNARK::verify(&vk.clone().into(), &[c], &proof).unwrap(),
            "The native verification check fails."
        );

        // Initialize constraint system.
        let mut cs = TestConstraintSystem::<Fq>::new();

        let input_gadget = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::InputVar::alloc(
            cs.ns(|| "alloc_input_gadget"),
            || Ok(vec![c]),
        )
        .unwrap();

        // TODO (raychu86): Should be allocated as input.
        // let input_gadget = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::InputVar::alloc_input(
        //     cs.ns(|| "alloc_input_gadget"),
        //     || Ok(vec![c]),
        // )
        //     .unwrap();

        let proof_gadget =
            <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::ProofVar::alloc(cs.ns(|| "alloc_proof"), || Ok(proof))
                .unwrap();

        let vk_gadget =
            <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::VerifyingKeyVar::alloc(cs.ns(|| "alloc_vk"), || {
                Ok(vk.clone())
            })
            .unwrap();

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );

        let verification_result = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::verify(
            cs.ns(|| "marlin_verify"),
            &vk_gadget,
            &input_gadget,
            &proof_gadget,
        )
        .unwrap();

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );

        verification_result
            .enforce_equal(cs.ns(|| "enforce_equal_verification"), &Boolean::Constant(true))
            .unwrap();

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );
    }

    #[test]
    fn partial_marlin_verifier_test() {
        let mut rng = test_rng();

        // Construct the circuit.

        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let mut c = a;
        c.mul_assign(&b);

        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints: 100,
            num_variables: 25,
        };

        // Generate the circuit parameters.

        let (pk, vk) = TestSNARK::circuit_specific_setup(circ, &mut rng).unwrap();

        // Test native proof and verification.

        let proof = TestSNARK::prove(&pk, &circ, &mut rng).unwrap();

        // assert!(
        //     TestSNARK::verify(&vk.clone().into(), &[c.clone()], &proof).unwrap(),
        //     "The native verification check fails."
        // );

        let (lc_s, native_opening_challenges, native_comms, native_query_set, native_evals, _rng) =
            TestSNARK::partial_verify(&vk.clone().into(), &[c.clone()], &proof).unwrap();

        // Initialize constraint system.
        let mut cs = TestConstraintSystem::<Fq>::new();

        let input_gadget = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::InputVar::alloc(
            cs.ns(|| "alloc_input_gadget"),
            || Ok(vec![c]),
        )
        .unwrap();

        // TODO (raychu86): Should be allocated as input.
        // let input_gadget = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::InputVar::alloc_input(
        //     cs.ns(|| "alloc_input_gadget"),
        //     || Ok(vec![c]),
        // )
        // .unwrap();

        let proof_gadget =
            <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::ProofVar::alloc(cs.ns(|| "alloc_proof"), || {
                Ok(proof.clone())
            })
            .unwrap();

        let vk_gadget =
            <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::VerifyingKeyVar::alloc(cs.ns(|| "alloc_vk"), || {
                Ok(vk.clone())
            })
            .unwrap();

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );

        let public_input = &[c];

        let (
            lc_gadgets,
            gadget_opening_challenges,
            gadget_opening_challenge_bits,
            gadget_commitments,
            gadget_query_set,
            gadget_evaluations,
        ) = TestSNARKGadget::partial_verify(
            cs.ns(|| "marlin_partial_verify"),
            &vk,
            &vk_gadget,
            &input_gadget,
            &proof_gadget,
        )
        .unwrap();

        // let first_round_message_gadget = verifier_state_gadget.first_round_msg.clone().unwrap();
        // let second_round_message_gadget = verifier_state_gadget.second_round_msg.clone().unwrap();
        // let first_round_message = verifier_state_native.first_round_message.unwrap();
        // let second_round_message = verifier_state_native.second_round_message.unwrap();
        //
        // let expected_alpha = NonNativeFieldVar::alloc(cs.ns(|| "alpha"), || Ok(first_round_message.alpha)).unwrap();
        // let expected_eta_a = NonNativeFieldVar::alloc(cs.ns(|| "eta_a"), || Ok(first_round_message.eta_a)).unwrap();
        // let expected_eta_b = NonNativeFieldVar::alloc(cs.ns(|| "eta_b"), || Ok(first_round_message.eta_b)).unwrap();
        // let expected_eta_c = NonNativeFieldVar::alloc(cs.ns(|| "eta_c"), || Ok(first_round_message.eta_c)).unwrap();
        //
        // expected_alpha
        //     .enforce_equal(cs.ns(|| "enforce_equal_alpha"), &first_round_message_gadget.alpha)
        //     .unwrap();
        // expected_eta_a
        //     .enforce_equal(cs.ns(|| "enforce_equal_eta_a"), &first_round_message_gadget.eta_a)
        //     .unwrap();
        // expected_eta_b
        //     .enforce_equal(cs.ns(|| "enforce_equal_eta_b"), &first_round_message_gadget.eta_b)
        //     .unwrap();
        // expected_eta_c
        //     .enforce_equal(cs.ns(|| "enforce_equal_eta_c"), &first_round_message_gadget.eta_c)
        //     .unwrap();
        //
        // // Enforce that the native and gadget verifier first round state is equivalent.
        //
        // let expected_beta = NonNativeFieldVar::alloc(cs.ns(|| "beta"), || Ok(second_round_message.beta)).unwrap();
        //
        // expected_beta
        //     .enforce_equal(cs.ns(|| "enforce_equal_beta"), &second_round_message_gadget.beta)
        //     .unwrap();
        //
        // let expected_gamma =
        //     NonNativeFieldVar::alloc(cs.ns(|| "gamma"), || Ok(verifier_state_native.gamma.unwrap())).unwrap();
        //
        // expected_gamma
        //     .enforce_equal(
        //         cs.ns(|| "enforce_equal_gamma"),
        //         &verifier_state_gadget.gamma.clone().unwrap(),
        //     )
        //     .unwrap();
        //
        // // Enforce that the native and gadget verifier first round state is equivalent.
        //
        // assert_eq!(
        //     verifier_state_native.first_round_message.is_some(),
        //     verifier_state_gadget.first_round_msg.is_some()
        // );
        // assert_eq!(
        //     verifier_state_native.second_round_message.is_some(),
        //     verifier_state_gadget.second_round_msg.is_some()
        // );
        // assert_eq!(
        //     verifier_state_native.gamma.is_some(),
        //     verifier_state_gadget.gamma.is_some()
        // );
        //
        // if !cs.is_satisfied() {
        //     println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        // }
        //
        // assert!(cs.is_satisfied());

        // // ---- Gadget verification
        //
        // let verification_result = <TestSNARKGadget as SNARKGadget<Fr, Fq, TestSNARK>>::verify(
        //     cs.ns(|| "marlin_verify"),
        //     &vk_gadget,
        //     &input_gadget,
        //     &proof_gadget,
        // )
        // .unwrap();

        // Check that the lc decision is valid

        for (i, (native_lc, lc)) in lc_s.iter().zip(lc_gadgets).enumerate() {
            let expected_lc =
                LinearCombinationVar::alloc(cs.ns(|| format!("alloc_lc_{}", i)), || Ok(native_lc)).unwrap();

            assert_eq!(expected_lc.label, lc.label);

            for (j, ((expected_lc_coeff, expected_lc_term), (lc_coeff, lc_term))) in
                expected_lc.terms.iter().zip(lc.terms).enumerate()
            {
                assert_eq!(expected_lc_term, &lc_term);

                match (expected_lc_coeff, &lc_coeff) {
                    (LinearCombinationCoeffVar::MinusOne, LinearCombinationCoeffVar::MinusOne) => {}
                    (LinearCombinationCoeffVar::One, LinearCombinationCoeffVar::One) => {}
                    (LinearCombinationCoeffVar::Var(expected_coeff), LinearCombinationCoeffVar::Var(coeff)) => {
                        expected_coeff
                            .enforce_equal(cs.ns(|| format!("enforce_eq_coeff_{}_{}", i, j)), &coeff)
                            .unwrap();
                    }
                    (LinearCombinationCoeffVar::Var(expected_coeff), LinearCombinationCoeffVar::One) => {
                        let one = NonNativeFieldVar::one(cs.ns(|| format!("testing_{}_{}", i, j))).unwrap();
                        expected_coeff
                            .enforce_equal(cs.ns(|| format!("enforce_eq_coeff_one_{}_{}", i, j)), &one)
                            .unwrap();
                    }
                    (_, _) => {
                        println!(
                            "Mismatched linear combination coeff_{}_{} \n{:?} \n{:?}",
                            i, j, expected_lc_coeff, lc_coeff
                        );
                        assert_eq!(0, 1);
                    }
                }
            }
        }

        // Check challenge gadget

        println!("Checking opening challenges");

        let mut expected_opening_challenges = Vec::new();

        for (i, (challenge, challenge_gadget)) in native_opening_challenges
            .iter()
            .zip(gadget_opening_challenges)
            .enumerate()
        {
            let expected_gadget =
                NonNativeFieldVar::alloc(cs.ns(|| format!("challenge_{}", i)), || Ok(challenge)).unwrap();

            expected_gadget
                .enforce_equal(
                    cs.ns(|| format!("enforce_eq_opening_challenge_{}", i)),
                    &challenge_gadget,
                )
                .unwrap();

            expected_opening_challenges.push(expected_gadget);
        }

        // Check query set gadgets

        println!("Checking query set");

        let mut sorted_query_set_gadgets: Vec<_> = gadget_query_set.0.iter().collect();
        sorted_query_set_gadgets.sort_by(|a, b| a.0.cmp(&b.0));

        for (i, (query_native, query_gadget)) in native_query_set.iter().zip(sorted_query_set_gadgets).enumerate() {
            assert_eq!(query_native.0, query_gadget.0);

            let expected_query =
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_query{}", i)), || Ok(query_native.1)).unwrap();

            expected_query
                .enforce_equal(cs.ns(|| format!("enforce_eq_query_{}", i)), &query_gadget.1.value)
                .unwrap();
        }

        // Check that the commitments are equivalent

        println!("Checking commitments");

        for (i, (commitment_native, commitment_gadget)) in native_comms.iter().zip(gadget_commitments).enumerate() {
            // Check the label

            assert_eq!(commitment_native.label(), &commitment_gadget.label);

            // Check the commitment values
            let expected_commitment = LabeledCommitmentVar::<Bls12_377, BW6_761, Bls12_377PairingGadget>::alloc(
                cs.ns(|| format!("alloc_commitment_{}", i)),
                || Ok(commitment_native),
            )
            .unwrap();

            let expected_prepared_commitment = PreparedCommitmentVar::prepare(
                cs.ns(|| format!("prepare_comm_{}", i)),
                &expected_commitment.commitment,
            )
            .unwrap();

            expected_prepared_commitment
                .prepared_comm
                .enforce_equal(
                    cs.ns(|| format!("enforce_eq_commitment_comm{}", i)),
                    &commitment_gadget.prepared_commitment.prepared_comm,
                )
                .unwrap();

            assert_eq!(
                expected_prepared_commitment.shifted_comm.is_some(),
                commitment_gadget.prepared_commitment.shifted_comm.is_some()
            );

            if let (Some(expected_shifted_comm), Some(shifted_comm)) = (
                expected_prepared_commitment.shifted_comm,
                commitment_gadget.prepared_commitment.shifted_comm,
            ) {
                expected_shifted_comm
                    .enforce_equal(
                        cs.ns(|| format!("enforce_eq_commitment_shifted_comm{}", i)),
                        &shifted_comm,
                    )
                    .unwrap();
            }

            // Check degree bound.

            assert_eq!(
                expected_commitment.degree_bound.is_some(),
                commitment_gadget.degree_bound.is_some()
            );

            if let (Some(expected_degree_bound), Some(degree_bound_gadget)) =
                (expected_commitment.degree_bound, commitment_gadget.degree_bound)
            {
                expected_degree_bound
                    .enforce_equal(
                        cs.ns(|| format!("degree_bound_enforce_equal_{}", i)),
                        &degree_bound_gadget,
                    )
                    .unwrap();
            }
        }

        // Check that the evaluations are equivalent

        println!("Checking evaluations");

        let mut sorted_evaluation_gadgets: Vec<_> = gadget_evaluations.0.iter().collect();
        sorted_evaluation_gadgets.sort_by(|a, b| a.0.name.cmp(&b.0.name));

        for (i, (evaluation_native, evaluation_gadget)) in
            native_evals.iter().zip(sorted_evaluation_gadgets).enumerate()
        {
            assert_eq!(evaluation_native.0.0, evaluation_gadget.0.name);

            let expected_eval_key =
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_eval_key_{}", i)), || Ok(evaluation_native.0.1))
                    .unwrap();

            let expected_eval_value =
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_eval_value_{}", i)), || Ok(evaluation_native.1))
                    .unwrap();

            expected_eval_key
                .enforce_equal(
                    cs.ns(|| format!("enforce_eq_eval_key_{}", i)),
                    &evaluation_gadget.0.value,
                )
                .unwrap();

            expected_eval_value
                .enforce_equal(cs.ns(|| format!("enforce_eq_eval_value_{}", i)), &evaluation_gadget.1)
                .unwrap();
        }

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );

        // BEGIN: proof to proof_gadget
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = proof.clone();

        let commitment_gadgets: Vec<Vec<CommitmentVar<Bls12_377, BW6_761, Bls12_377PairingGadget>>> = commitments
            .iter()
            .enumerate()
            .map(|(i, lst)| {
                lst.iter()
                    .enumerate()
                    .map(|(j, comm)| {
                        CommitmentVar::alloc(cs.ns(|| format!("alloc_commitment_{}_{}", i, j)), || Ok(comm)).unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<Fr, Fq>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_evaluation_{}", i)), || Ok(eval)).unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMessageVar<Fr, Fq>> = prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldVar<Fr, Fq>> = msg
                    .field_elements
                    .iter()
                    .enumerate()
                    .map(|(j, elem)| {
                        NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_message_{}_{}", i, j)), || Ok(elem)).unwrap()
                    })
                    .collect();

                ProverMessageVar { field_elements }
            })
            .collect();

        let pc_batch_proof =
            BatchLCProofVar::<Bls12_377, BW6_761, Bls12_377PairingGadget>::alloc(cs.ns(|| "batch_proof"), || {
                Ok(pc_proof)
            })
            .unwrap();

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldVar<Fr, Fq>>::new();

        const ALL_POLYNOMIALS: [&str; 10] = [
            "a_denom",
            "b_denom",
            "c_denom",
            "g_1",
            "g_2",
            "t",
            "vanishing_poly_h_alpha",
            "vanishing_poly_h_beta",
            "vanishing_poly_k_gamma",
            "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        let manually_constructed_proof_gadget: ProofVar<Fr, Fq, PC, PCGadget> = ProofVar {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        };

        // let (
        //     lc_gadgets,
        //     gadget_opening_challenges,
        //     gadget_opening_challenge_bits,
        //     gadget_commitments,
        //     gadget_query_set,
        //     gadget_evaluations,
        // ) = TestSNARKGadget::partial_verify(
        //     cs.ns(|| "marlin_partial_verify_2"),
        //     &vk,
        //     &vk_gadget,
        //     &input_gadget,
        //     &manually_constructed_proof_gadget,
        // )
        // .unwrap();
        // END: proof to proof_gadget

        // What can i do to check -
        //  1. Try to do native verifier check (or challenge checks) using the .value() from the gadgets
        //  2. Try to do gadget verifier check inside the native verifier (alloc the native elements).

        // let (lc_s, native_opening_challenges, native_comms, native_query_set, native_evals, fs_rng) =
        //     TestSNARK::partial_verify(&vk.clone().into(), &[c.clone()], &proof).unwrap();
        //
        // let prepared_verifying_key_gadget =
        //     PreparedCircuitVerifyingKeyVar::<Fr, Fq, PC, PCGadget, FS, FSG>::prepare(cs.ns(|| "prepare"), &vk_gadget)
        //         .unwrap();
        //
        // let mut fs_rng_gadget = FSG::constant(cs.ns(|| "constant"), &fs_rng);
        //
        // let (batching_rands, batching_rands_bits) = fs_rng_gadget
        //     .squeeze_128_bits_field_elements_and_bits(cs.ns(|| "batching_squeeze_128_bits_field_elements_and_bits"), 2)
        //     .unwrap();
        //
        // let rand_data = PCCheckRandomDataVar::<Fr, Fq> {
        //     opening_challenges: gadget_opening_challenges.clone(),
        //     opening_challenges_bits: gadget_opening_challenge_bits.clone(),
        //     batching_rands,
        //     batching_rands_bits,
        // };
        //
        // let eval = PCGadget::prepared_check_combinations(
        //     cs.ns(|| "prepared_check_combinations"),
        //     &prepared_verifying_key_gadget.prepared_verifier_key,
        //     &lc_gadgets,         // Checked
        //     &gadget_commitments, // Checked
        //     &gadget_query_set,   // Checked
        //     &gadget_evaluations, // Checked
        //     &proof_gadget.pc_batch_proof,
        //     &rand_data,
        // )
        // .unwrap();
        //
        // println!("Eval is: {:?}", eval);
    }
}
