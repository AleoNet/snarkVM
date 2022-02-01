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
    fiat_shamir::FiatShamirRng,
    marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinMode, PreparedCircuitVerifyingKey, Proof},
};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, SNARKError, SNARK, SRS};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_polycommit::PolynomialCommitment;
use snarkvm_r1cs::ConstraintSynthesizer;

use core::sync::atomic::AtomicBool;
use rand::{CryptoRng, Rng};

impl<TargetField, BaseField, PC, FS, MM, Input> SNARK
    for crate::marlin::MarlinSNARK<TargetField, BaseField, PC, FS, MM, Input>
where
    TargetField: PrimeField,
    BaseField: PrimeField + PoseidonDefaultParametersField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    FS: FiatShamirRng<TargetField, BaseField>,
    MM: MarlinMode,
    Input: ToConstraintField<TargetField>,
{
    type BaseField = BaseField;
    type PreparedVerifyingKey = PreparedCircuitVerifyingKey<TargetField, BaseField, PC, MM>;
    type Proof = Proof<TargetField, BaseField, PC>;
    type ProvingKey = CircuitProvingKey<TargetField, BaseField, PC, MM>;
    type ScalarField = TargetField;
    type UniversalSetupConfig = usize;
    type UniversalSetupParameters = crate::marlin::UniversalSRS<TargetField, BaseField, PC>;
    type VerifierInput = Input;
    type VerifyingKey = CircuitVerifyingKey<TargetField, BaseField, PC, MM>;

    fn universal_setup<R: Rng + CryptoRng>(
        max_degree: &Self::UniversalSetupConfig,
        rng: &mut R,
    ) -> Result<Self::UniversalSetupParameters, SNARKError> {
        let setup_time = start_timer!(|| "{Marlin}::Setup");
        let srs = Self::universal_setup(*max_degree, rng)?;
        end_timer!(setup_time);

        Ok(srs)
    }

    fn setup<C: ConstraintSynthesizer<TargetField>, R: Rng + CryptoRng>(
        circuit: &C,
        srs: &mut SRS<R, Self::UniversalSetupParameters>,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), SNARKError> {
        match srs {
            SRS::CircuitSpecific(rng) => Self::circuit_specific_setup(circuit, rng),
            SRS::Universal(srs) => Self::circuit_setup(srs, circuit),
        }
        .map_err(SNARKError::from)
    }

    fn prove_with_terminator<C: ConstraintSynthesizer<TargetField>, R: Rng + CryptoRng>(
        parameters: &Self::ProvingKey,
        circuit: &C,
        terminator: &AtomicBool,
        rng: &mut R,
    ) -> Result<Self::Proof, SNARKError> {
        Self::prove_with_terminator(parameters, circuit, terminator, rng).map_err(SNARKError::from)
    }

    fn verify_prepared(
        prepared_verifying_key: &Self::PreparedVerifyingKey,
        input: &Self::VerifierInput,
        proof: &Self::Proof,
    ) -> Result<bool, SNARKError> {
        Self::prepared_verify(prepared_verifying_key, &input.to_field_elements()?, proof).map_err(SNARKError::from)
    }
}

#[cfg(test)]
pub mod test {
    use core::ops::MulAssign;

    use super::*;
    use crate::{
        fiat_shamir::FiatShamirAlgebraicSpongeRng,
        marlin::{MarlinHidingMode, MarlinSNARK},
    };
    use snarkvm_algorithms::{crypto_hash::poseidon::PoseidonSponge, SRS};
    use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
    use snarkvm_fields::Field;
    use snarkvm_polycommit::sonic_pc::SonicKZG10;
    use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    #[derive(Copy, Clone)]
    pub struct Circuit<F: Field> {
        pub a: Option<F>,
        pub b: Option<F>,
        pub num_constraints: usize,
        pub num_variables: usize,
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
                let _ = cs.alloc(|| format!("var {}", i), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for i in 0..(self.num_constraints - 1) {
                cs.enforce(|| format!("constraint {}", i), |lc| lc + a, |lc| lc + b, |lc| lc + c);
            }

            Ok(())
        }
    }

    type PC = SonicKZG10<Bls12_377>;
    type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
    type TestSNARK = MarlinSNARK<Fr, Fq, PC, FS, MarlinHidingMode, Vec<Fr>>;

    #[test]
    fn marlin_snark_test() {
        let mut rng = test_rng();

        for _ in 0..ITERATIONS {
            // Construct the circuit.

            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);
            let mut c = a;
            c.mul_assign(&b);

            let circ = Circuit { a: Some(a), b: Some(b), num_constraints: 100, num_variables: 25 };

            // Generate the circuit parameters.

            let (pk, vk) = TestSNARK::setup(&circ, &mut SRS::CircuitSpecific(&mut rng)).unwrap();

            // Test native proof and verification.

            let proof = TestSNARK::prove(&pk, &circ, &mut rng).unwrap();

            assert!(TestSNARK::verify(&vk.clone(), &[c], &proof).unwrap(), "The native verification check fails.");
        }
    }
}
