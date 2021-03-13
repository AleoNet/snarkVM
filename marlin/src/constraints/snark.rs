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
        data_structures::{CircuitVerifyingKeyVar, PreparedCircuitVerifyingKeyVar, ProofVar, UniversalSRS},
        verifier::MarlinVerificationGadget,
    },
    fiat_shamir::{constraints::FiatShamirRngVar, FiatShamirRng},
    marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinConfig, MarlinCore, PreparedCircuitVerifyingKey, Proof},
};
use snarkvm_algorithms::{SNARKError, SNARK};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::traits::{
    fields::{FieldGadget, ToConstraintFieldGadget},
    utilities::boolean::Boolean,
};
use snarkvm_nonnative::NonNativeFieldInputVar;
use snarkvm_polycommit::{constraints::PCCheckVar, LinearCombination, PolynomialCommitment};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, Variable};
use snarkvm_utilities::test_rng;

use rand::{Rng, RngCore};

use crate::marlin::MarlinError;
use std::{
    cmp::min,
    fmt::{Debug, Formatter},
    marker::PhantomData,
};

#[derive(Clone, PartialEq, PartialOrd)]
pub struct MarlinBound {
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

pub struct MarlinSNARK<
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F>,
    FS: FiatShamirRng<F, FSF>,
    MC: MarlinConfig,
    C: ConstraintSynthesizer<FSF>,
> {
    f_phantom: PhantomData<F>,
    fsf_phantom: PhantomData<FSF>,
    pc_phantom: PhantomData<PC>,
    fs_phantom: PhantomData<FS>,
    mc_phantom: PhantomData<MC>,
    c_phantom: PhantomData<C>,
}

impl<TargetField, BaseField, PC, FS, MC, C> MarlinSNARK<TargetField, BaseField, PC, FS, MC, C>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MC: MarlinConfig,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    // fn universal_setup<R: Rng>(
    //     bound: &MarlinBound,
    //     rng: &mut R,
    // ) -> Result<(MarlinBound, UniversalSRS<TargetField, PC>), Box<MarlinConstraintsError>> {
    //     let MarlinBound { max_degree } = bound;
    //
    //     match MarlinCore::<TargetField, BaseField, PC, FS, MC>::universal_setup(1, 1, (max_degree + 5) / 3, rng) {
    //         Ok(res) => Ok((bound.clone(), res)),
    //         Err(e) => Err(Box::new(MarlinError::from(e))),
    //     }
    // }
    //
    // #[allow(clippy::type_complexity)]
    // fn index<C: ConstraintSynthesizer<TargetField>, R: RngCore>(
    //     crs: &(MarlinBound, UniversalSRS<TargetField, PC>),
    //     circuit: C,
    //     _rng: &mut R,
    // ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Box<MarlinConstraintsError>> {
    //     let index_res = MarlinCore::<TargetField, BaseField, PC, FS, MC>::index(&crs.1, circuit);
    //     match index_res {
    //         Ok(res) => Ok(res),
    //         Err(err) => match err {
    //             IndexTooLarge(v) => Err(UniversalSetupIndexError::NeedLargerBound(MarlinBound { max_degree: v })),
    //             _ => Err(UniversalSetupIndexError::Other(Box::new(MarlinError::from(err)))),
    //         },
    //     }
    // }
    //
    // fn circuit_specific_setup<C: ConstraintSynthesizer<TargetField>, R: RngCore + CryptoRng>(
    //     circuit: C,
    //     rng: &mut R,
    // ) -> Result<(CircuitProvingKey<TargetField, PC>, CircuitVerifyingKey<TargetField, PC>), Box<MarlinConstraintsError>>
    // {
    //     Ok(MarlinCore::<TargetField, BaseField, PC, FS, MC>::circuit_specific_setup(circuit, rng).unwrap())
    // }

    fn process_vk(
        vk: &Self::VerifyingKey,
    ) -> Result<PreparedCircuitVerifyingKey<TargetField, PC>, Box<MarlinConstraintsError>> {
        Ok(PreparedCircuitVerifyingKey::prepare(vk))
    }

    fn verify_with_processed_vk(
        pvk: &PreparedCircuitVerifyingKey<TargetField, PC>,
        x: &[TargetField],
        proof: &Proof<TargetField, PC>,
    ) -> Result<bool, Box<MarlinConstraintsError>> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MC>::prepared_verify(pvk, x, proof) {
            Ok(res) => Ok(res),
            Err(e) => Err(Box::new(MarlinError::from(e).into())),
        }
    }
}

impl<TargetField, BaseField, PC, FS, MC, C> SNARK for MarlinSNARK<TargetField, BaseField, PC, FS, MC, C>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MC: MarlinConfig,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    type AllocatedCircuit = C;
    type Circuit = (C, UniversalSRS<TargetField, PC>);
    type PreparedVerifyingKey = CircuitVerifyingKey<TargetField, PC>;
    type Proof = Proof<TargetField, PC>;
    type ProvingKey = CircuitProvingKey<TargetField, PC>;
    type VerifierInput = &'static [TargetField];
    type VerifyingKey = CircuitVerifyingKey<TargetField, PC>;

    fn setup<R: RngCore>(
        (circuit, srs): &Self::Circuit,
        rng: &mut R, // The Marlin circuit setup is deterministic.
    ) -> Result<(Self::ProvingKey, Self::PreparedVerifyingKey), Self::Error> {
        // let setup_time = start_timer!(|| "{Marlin}::Setup");
        // let parameters = Parameters::<E>::new(circuit, srs)?;
        // end_timer!(setup_time);
        //
        // let verifying_key = parameters.verifying_key.clone();
        // Ok((parameters, verifying_key))
        Ok(MarlinCore::<TargetField, BaseField, PC, FS, MC>::circuit_specific_setup(circuit, rng).unwrap())
    }

    fn prove<R: Rng>(
        parameters: &Self::ProvingKey,
        circuit: &Self::AllocatedCircuit,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MC>::prove(&parameters, circuit, rng) {
            Ok(res) => Ok(res),
            Err(e) => Err(SNARKError::from(e)),
        }
    }

    fn verify(
        verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        match MarlinCore::<TargetField, BaseField, PC, FS, MC>::verify(verifying_key, input, proof) {
            Ok(res) => Ok(res),
            Err(e) => Err(SNARKError::from(e)),
        }
    }
}

pub struct MarlinSNARKGadget<F, FSF, PC, FS, MC, PCG, FSG>
where
    F: PrimeField,
    FSF: PrimeField,
    PC: PolynomialCommitment<F>,
    FS: FiatShamirRng<F, FSF>,
    MC: MarlinConfig,
    PCG: PCCheckVar<F, PC, FSF>,
    FSG: FiatShamirRngVar<F, FSF, FS>,
{
    f_phantom: PhantomData<F>,
    fsf_phantom: PhantomData<FSF>,
    pc_phantom: PhantomData<PC>,
    fs_phantom: PhantomData<FS>,
    mc_phantom: PhantomData<MC>,
    pcg_phantom: PhantomData<PCG>,
    fsg_phantom: PhantomData<FSG>,
}

impl<TargetField, BaseField, PC, FS, MC, PCG, FSG, C>
    SNARKGadget<TargetField, BaseField, MarlinSNARK<TargetField, BaseField, PC, FS, MC, C>>
    for MarlinSNARKGadget<TargetField, BaseField, PC, FS, MC, PCG, FSG>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MC: MarlinConfig,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    FSG: FiatShamirRngVar<TargetField, BaseField, FS>,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
    C: ConstraintSynthesizer<TargetField>,
{
    type InputVar = NonNativeFieldInputVar<TargetField, BaseField>;
    type ProcessedVerifyingKeyVar = PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, FS, FSG>;
    type ProofVar = ProofVar<TargetField, BaseField, PC, PCG>;
    type VerifierSize = usize;
    type VerifyingKeyVar = CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>;

    fn verifier_size(
        circuit_vk: &<MarlinSNARK<TargetField, BaseField, PC, FS, MC, C> as SNARK>::VerifyingKey,
    ) -> Self::VerifierSize {
        circuit_vk.circuit_info.num_instance_variables
    }

    fn verify_with_processed_vk(
        circuit_pvk: &Self::ProcessedVerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError> {
        Ok(
            MarlinVerificationGadget::<TargetField, BaseField, PC, PCG>::prepared_verify(&circuit_pvk, &x.val, proof)
                .unwrap(),
        )
    }

    fn verify(
        circuit_vk: &Self::VerifyingKeyVar,
        x: &Self::InputVar,
        proof: &Self::ProofVar,
    ) -> Result<Boolean, SynthesisError> {
        Ok(
            MarlinVerificationGadget::<TargetField, BaseField, PC, PCG>::verify::<_, FS, FSG>(
                circuit_vk, &x.val, proof,
            )
            .unwrap(),
        )
    }
}

#[derive(Clone)]
pub struct MarlinBoundCircuit<F: PrimeField> {
    pub bound: MarlinBound,
    pub fsf_phantom: PhantomData<F>,
}

impl<F: PrimeField> From<MarlinBound> for MarlinBoundCircuit<F> {
    fn from(bound: MarlinBound) -> Self {
        Self {
            bound,
            fsf_phantom: PhantomData,
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for MarlinBoundCircuit<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let MarlinBound { max_degree } = self.bound;

        let num_variables = max_degree / 3;
        let num_constraints = max_degree / 3;

        let mut vars: Vec<Variable> = vec![];
        for _ in 0..num_variables - 1 {
            let var_i = cs.new_witness_variable(|| Ok(F::zero()))?;
            vars.push(var_i);
        }

        let mut rng = test_rng();

        let mut non_zero_remaining = (max_degree + 5) / 3;
        for i in 0..num_constraints {
            if non_zero_remaining > 0 {
                let num_for_this_constraint = min(non_zero_remaining, num_variables - 1);

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

// impl<F, FSF, PC, FS, MC, PCG, FSG> UniversalSetupSNARKGadget<F, FSF, MarlinSNARK<F, FSF, PC, FS, MC>>
//     for MarlinSNARKGadget<F, FSF, PC, FS, MC, PCG, FSG>
// where
//     F: PrimeField,
//     FSF: PrimeField,
//     PC: PolynomialCommitment<F>,
//     FS: FiatShamirRng<F, FSF>,
//     MC: MarlinConfig,
//     PCG: PCCheckVar<F, PC, FSF>,
//     FSG: FiatShamirRngVar<F, FSF, FS>,
//     PC::VerifierKey: ToConstraintField<FSF>,
//     PC::Commitment: ToConstraintField<FSF>,
//     PCG::VerifierKeyVar: ToConstraintFieldGadget<FSF>,
//     PCG::CommitmentVar: ToConstraintFieldGadget<FSF>,
// {
//     type BoundCircuit = MarlinBoundCircuit<F>;
// }

pub struct MarlinConstraintsError {
    pub error_msg: String,
}

impl<E> From<MarlinError<E>> for MarlinConstraintsError
where
    E: std::error::Error,
{
    fn from(e: MarlinError<E>) -> Self {
        match e {
            crate::marlin::MarlinError::<E>::IndexTooLarge(u, v) => Self {
                error_msg: format!("index of {} is too large, maximum degree of {}", v, u),
            },
            crate::marlin::MarlinError::<E>::AHPError(err) => match err {
                crate::ahp::AHPError::MissingEval(str) => Self {
                    error_msg: String::from("missing eval: ") + &*str,
                },
                crate::ahp::AHPError::InvalidPublicInputLength => Self {
                    error_msg: String::from("invalid public input length"),
                },
                crate::ahp::AHPError::InstanceDoesNotMatchIndex => Self {
                    error_msg: String::from("instance does not match index"),
                },
                crate::ahp::AHPError::NonSquareMatrix => Self {
                    error_msg: String::from("non-sqaure matrix"),
                },
                crate::ahp::AHPError::ConstraintSystemError(error) => Self {
                    error_msg: error.to_string(),
                },
            },
            crate::marlin::MarlinError::<E>::R1CSError(err) => Self {
                error_msg: err.to_string(),
            },
            crate::marlin::MarlinError::<E>::PolynomialCommitmentError(err) => Self {
                error_msg: err.to_string(),
            },
        }
    }
}

impl Debug for MarlinConstraintsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}

impl core::fmt::Display for MarlinConstraintsError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.error_msg)
    }
}

// #[cfg(test)]
// mod test {
//     use super::*;
//     use snarkvm_fields::Field;
//
//     use crate::MarlinConfig;
//     #[derive(Clone)]
//     struct TestMarlinConfig;
//     impl MarlinConfig for TestMarlinConfig {
//         const FOR_RECURSION: bool = true;
//     }
//
//     #[derive(Copy, Clone, Debug)]
//     struct Mnt64298cycle;
//     impl CurveCycle for Mnt64298cycle {
//         type E1 = <MNT6_298 as PairingEngine>::G1Affine;
//         type E2 = <MNT4_298 as PairingEngine>::G1Affine;
//     }
//     impl PairingFriendlyCycle for Mnt64298cycle {
//         type Engine1 = MNT6_298;
//         type Engine2 = MNT4_298;
//     }
//
//     // use crate::{
//     //     constraints::snark::{MarlinSNARK, MarlinSNARKGadget},
//     //     fiat_shamir::{
//     //         constraints::FiatShamirAlgebraicSpongeRngVar,
//     //         poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
//     //         FiatShamirAlgebraicSpongeRng,
//     //     },
//     // };
//     // use ark_crypto_primitives::snark::{SNARKGadget, SNARK};
//     // use ark_ec::{CurveCycle, PairingEngine, PairingFriendlyCycle};
//     // use ark_ff::{Field, UniformRand};
//     // use ark_mnt4_298::{constraints::PairingVar as MNT4PairingVar, Fq as MNT4Fq, Fr as MNT4Fr, MNT4_298};
//     // use ark_mnt6_298::MNT6_298;
//     // use ark_poly_commit::marlin_pc::{MarlinKZG10, MarlinKZG10Gadget};
//     // use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
//     // use ark_relations::{
//     //     lc, ns,
//     //     r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError},
//     // };
//     use core::ops::MulAssign;
//
//     #[derive(Copy, Clone)]
//     struct Circuit<F: Field> {
//         a: Option<F>,
//         b: Option<F>,
//         num_constraints: usize,
//         num_variables: usize,
//     }
//
//     impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
//         fn generate_constraints(self, cs: ConstraintSystemRef<ConstraintF>) -> Result<(), SynthesisError> {
//             let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
//             let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
//             let c = cs.new_input_variable(|| {
//                 let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
//                 let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;
//
//                 a.mul_assign(&b);
//                 Ok(a)
//             })?;
//
//             for _ in 0..(self.num_variables - 3) {
//                 let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
//             }
//
//             for _ in 0..self.num_constraints {
//                 cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c).unwrap();
//             }
//             Ok(())
//         }
//     }
//
//     type TestSNARK = MarlinSNARK<MNT4Fr, MNT4Fq, MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>>, FS4, TestMarlinConfig>;
//     type FS4 = FiatShamirAlgebraicSpongeRng<MNT4Fr, MNT4Fq, PoseidonSponge<MNT4Fq>>;
//     type PCGadget4 = MarlinKZG10Gadget<Mnt64298cycle, DensePolynomial<MNT4Fr>, MNT4PairingVar>;
//     type FSG4 = FiatShamirAlgebraicSpongeRngVar<MNT4Fr, MNT4Fq, PoseidonSponge<MNT4Fq>, PoseidonSpongeVar<MNT4Fq>>;
//     type TestSNARKGadget = MarlinSNARKGadget<
//         MNT4Fr,
//         MNT4Fq,
//         MarlinKZG10<MNT4_298, DensePolynomial<MNT4Fr>>,
//         FS4,
//         TestMarlinConfig,
//         PCGadget4,
//         FSG4,
//     >;
//
//     use ark_poly::univariate::DensePolynomial;
//     use ark_relations::r1cs::OptimizationGoal;
//
//     #[test]
//     fn marlin_snark_test() {
//         let mut rng = ark_std::test_rng();
//         let a = MNT4Fr::rand(&mut rng);
//         let b = MNT4Fr::rand(&mut rng);
//         let mut c = a;
//         c.mul_assign(&b);
//
//         let circ = Circuit {
//             a: Some(a),
//             b: Some(b),
//             num_constraints: 100,
//             num_variables: 25,
//         };
//
//         let (pk, vk) = TestSNARK::circuit_specific_setup(circ, &mut rng).unwrap();
//
//         let proof = TestSNARK::prove(&pk, circ, &mut rng).unwrap();
//
//         assert!(
//             TestSNARK::verify(&vk, &[c], &proof).unwrap(),
//             "The native verification check fails."
//         );
//
//         let cs_sys = ConstraintSystem::<MNT4Fq>::new();
//         let cs = ConstraintSystemRef::new(cs_sys);
//         cs.set_optimization_goal(OptimizationGoal::Weight);
//
//         let input_gadget = <TestSNARKGadget as SNARKGadget<
//             <MNT4_298 as PairingEngine>::Fr,
//             <MNT4_298 as PairingEngine>::Fq,
//             TestSNARK,
//         >>::InputVar::new_input(ns!(cs, "new_input"), || Ok(vec![c]))
//         .unwrap();
//
//         let proof_gadget = <TestSNARKGadget as SNARKGadget<
//             <MNT4_298 as PairingEngine>::Fr,
//             <MNT4_298 as PairingEngine>::Fq,
//             TestSNARK,
//         >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(proof))
//         .unwrap();
//         let vk_gadget = <TestSNARKGadget as SNARKGadget<
//             <MNT4_298 as PairingEngine>::Fr,
//             <MNT4_298 as PairingEngine>::Fq,
//             TestSNARK,
//         >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), vk.clone())
//         .unwrap();
//
//         assert!(
//             cs.is_satisfied().unwrap(),
//             "Constraints not satisfied: {}",
//             cs.which_is_unsatisfied().unwrap().unwrap_or_default()
//         );
//
//         let verification_result = <TestSNARKGadget as SNARKGadget<
//             <MNT4_298 as PairingEngine>::Fr,
//             <MNT4_298 as PairingEngine>::Fq,
//             TestSNARK,
//         >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
//         .unwrap();
//
//         assert!(
//             cs.is_satisfied().unwrap(),
//             "Constraints not satisfied: {}",
//             cs.which_is_unsatisfied().unwrap().unwrap_or_default()
//         );
//
//         verification_result.enforce_equal(&Boolean::Constant(true)).unwrap();
//
//         assert!(
//             cs.is_satisfied().unwrap(),
//             "Constraints not satisfied: {}",
//             cs.which_is_unsatisfied().unwrap().unwrap_or_default()
//         );
//
//         let pvk = TestSNARK::process_vk(&vk).unwrap();
//         let pvk_gadget = <TestSNARKGadget as SNARKGadget<
//             <MNT4_298 as PairingEngine>::Fr,
//             <MNT4_298 as PairingEngine>::Fq,
//             TestSNARK,
//         >>::ProcessedVerifyingKeyVar::new_constant(ns!(cs, "alloc_pvk"), pvk)
//         .unwrap();
//         TestSNARKGadget::verify_with_processed_vk(&pvk_gadget, &input_gadget, &proof_gadget)
//             .unwrap()
//             .enforce_equal(&Boolean::Constant(true))
//             .unwrap();
//
//         assert!(
//             cs.is_satisfied().unwrap(),
//             "Constraints not satisfied: {}",
//             cs.which_is_unsatisfied().unwrap().unwrap_or_default()
//         );
//     }
// }
