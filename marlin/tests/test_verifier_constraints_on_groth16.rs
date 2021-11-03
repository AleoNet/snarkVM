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

use snarkvm_algorithms::{snark::groth16::Groth16, SNARK, SRS};
use snarkvm_fields::{Field, PrimeField};
use snarkvm_gadgets::{
    curves::bls12_377::PairingGadget as Bls12_377PairingGadget,
    nonnative::NonNativeFieldVar,
    traits::alloc::AllocGadget,
    Boolean,
    EqGadget,
    FieldGadget,
    FpGadget,
};
use snarkvm_marlin::{
    constraints::{proof::ProofVar, verifier::MarlinVerificationGadget, verifier_key::CircuitVerifyingKeyVar},
    marlin::CircuitVerifyingKey,
    FiatShamirAlgebraicSpongeRng,
    FiatShamirAlgebraicSpongeRngVar,
    PoseidonSponge,
    PoseidonSpongeVar,
};
use snarkvm_polycommit::sonic_pc::{sonic_kzg10::SonicKZG10Gadget, SonicKZG10};
use snarkvm_r1cs::{
    ConstraintSynthesizer,
    ConstraintSystem,
    Index,
    LinearCombination,
    SynthesisError,
    TestConstraintChecker,
    TestConstraintSystem,
    Variable,
};
use snarkvm_utilities::{rand::UniformRand, test_rng};

use snarkvm_curves::{
    bls12_377::{Bls12_377, Fq, Fr},
    bw6_761::BW6_761,
};
use snarkvm_marlin::marlin::{MarlinRecursiveMode, MarlinSNARK as MarlinCore, Proof};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraints<F: PrimeField> {
    pub num_public_variables: usize,
    pub num_private_variables: usize,
    pub at: Vec<Vec<(F, Index)>>,
    pub bt: Vec<Vec<(F, Index)>>,
    pub ct: Vec<Vec<(F, Index)>>,
}

impl<F: PrimeField> Constraints<F> {
    fn new() -> Self {
        Self {
            num_private_variables: 0,
            num_public_variables: 1,
            at: Vec::new(),
            bt: Vec::new(),
            ct: Vec::new(),
        }
    }

    fn diff(&self, other: &Self) -> Option<usize> {
        for (i, (self_a, other_a)) in self.at.iter().zip(&other.at).enumerate() {
            if self_a != other_a {
                println!("Differed at row {} of A", i);
                return Some(i);
            }
        }
        for (i, (self_b, other_b)) in self.bt.iter().zip(&other.bt).enumerate() {
            if self_b != other_b {
                println!("Differed at row {} of B", i);
                println!(
                    "In 1: {:?}",
                    self_b.iter().map(|(f, ind)| (f.to_repr(), ind)).collect::<Vec<_>>()
                );
                println!(
                    "In 2: {:?}",
                    other_b.iter().map(|(f, ind)| (f.to_repr(), ind)).collect::<Vec<_>>()
                );
                return Some(i);
            }
        }
        for (i, (self_c, other_c)) in self.ct.iter().zip(&other.ct).enumerate() {
            if self_c != other_c {
                println!("Differed at row {} of C", i);
                return Some(i);
            }
        }
        None
    }
}

impl<CF: PrimeField> ConstraintSystem<CF> for Constraints<CF> {
    type Root = Self;

    #[inline]
    fn alloc<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<CF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: AsRef<str>,
    {
        // There is no assignment, so we don't invoke the
        // function for obtaining one.

        let index = self.num_private_variables;
        self.num_private_variables += 1;

        Ok(Variable::new_unchecked(Index::Private(index)))
    }

    #[inline]
    fn alloc_input<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<CF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: AsRef<str>,
    {
        // There is no assignment, so we don't invoke the
        // function for obtaining one.

        let index = self.num_public_variables;
        self.num_public_variables += 1;

        Ok(Variable::new_unchecked(Index::Public(index)))
    }

    #[inline]
    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: AsRef<str>,
        LA: FnOnce(LinearCombination<CF>) -> LinearCombination<CF>,
        LB: FnOnce(LinearCombination<CF>) -> LinearCombination<CF>,
        LC: FnOnce(LinearCombination<CF>) -> LinearCombination<CF>,
    {
        push_constraints(a(LinearCombination::zero()), &mut self.at);
        push_constraints(b(LinearCombination::zero()), &mut self.bt);
        push_constraints(c(LinearCombination::zero()), &mut self.ct);
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: AsRef<str>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self) {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn num_constraints(&self) -> usize {
        self.at.len()
    }

    fn num_public_variables(&self) -> usize {
        self.num_public_variables
    }

    fn num_private_variables(&self) -> usize {
        self.num_private_variables
    }

    fn is_in_setup_mode(&self) -> bool {
        true
    }
}

fn push_constraints<F: Field>(l: LinearCombination<F>, constraints: &mut Vec<Vec<(F, Index)>>) {
    let vars_and_coeffs = l.as_ref();
    let mut vec = Vec::with_capacity(vars_and_coeffs.len());

    for (var, coeff) in vars_and_coeffs {
        match var.get_unchecked() {
            Index::Public(i) => vec.push((*coeff, Index::Public(i))),
            Index::Private(i) => vec.push((*coeff, Index::Private(i))),
        }
    }
    constraints.push(vec);
}

#[derive(Clone, Debug)]
struct MulCircuit {
    pub a: Option<Fr>,
    pub b: Option<Fr>,
    pub c: Option<Fr>,
}

#[derive(Clone, Debug)]
struct MulSquareCircuit {
    pub a: Option<Fr>,
    pub b: Option<Fr>,
    pub c: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for MulCircuit {
    fn generate_constraints<CS: ConstraintSystem<Fr>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = FpGadget::alloc_input(&mut cs.ns(|| "a"), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = FpGadget::alloc_input(&mut cs.ns(|| "b"), || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = FpGadget::alloc_input(&mut cs.ns(|| "c"), || self.c.ok_or(SynthesisError::AssignmentMissing))?;

        let claimed_c = a.mul(cs.ns(|| "a * b"), &b)?;
        c.enforce_equal(cs.ns(|| "c == e"), &claimed_c)?;
        Ok(())
    }
}

impl ConstraintSynthesizer<Fr> for MulSquareCircuit {
    fn generate_constraints<CS: ConstraintSystem<Fr>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = FpGadget::alloc_input(&mut cs.ns(|| "a"), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = FpGadget::alloc_input(&mut cs.ns(|| "b"), || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = FpGadget::alloc_input(&mut cs.ns(|| "c"), || self.c.ok_or(SynthesisError::AssignmentMissing))?;

        let claimed_c = a.mul(cs.ns(|| "a * b"), &b)?.square(cs.ns(|| "d.square()"))?;
        c.enforce_equal(cs.ns(|| "c == e"), &claimed_c)?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct RecursiveCircuit {
    pub vk: Option<CircuitVerifyingKey<Fr, Fq, PC>>,
    pub input: Option<Vec<Fr>>,
    pub proof: Option<Proof<Fr, Fq, PC>>,
}

impl RecursiveCircuit {
    fn public_input(&self) -> Vec<Fq> {
        let mut cs = TestConstraintChecker::new();
        self.generate_constraints(&mut cs).unwrap();
        cs.public_inputs()
    }

    fn diff(&self, other: &Self) {
        let mut test_cs1 = TestConstraintSystem::new();
        self.generate_constraints(&mut test_cs1).unwrap();
        let mut test_cs2 = TestConstraintSystem::new();
        other.generate_constraints(&mut test_cs2).unwrap();
        println!("\n\n\n\n#############################################");
        // println!("\n\n\nDiffing now with TestConstraintSystem!!!");
        // test_cs1.diff(&test_cs2);
        // println!("\n\n\nDone diffing now!!!");
        // println!("Num_constraints: {}", test_cs1.num_constraints());

        println!("\n\n\nDiffing now with Constraints!!!");
        let mut cs1 = Constraints::new();
        self.generate_constraints(&mut cs1).unwrap();
        let mut cs2 = Constraints::new();
        other.generate_constraints(&mut cs2).unwrap();
        let diff_index = cs1.diff(&cs2);
        if let Some(i) = diff_index {
            println!("Differing constraint:");
            println!("In 1: {}", test_cs1.get_constraint_path(i));
            println!("In 2: {}", test_cs2.get_constraint_path(i));
        }
        println!("\n\n\nDone diffing now!!!");
    }
}

impl ConstraintSynthesizer<Fq> for RecursiveCircuit {
    fn generate_constraints<CS: ConstraintSystem<Fq>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let vk = CircuitVerifyingKeyVar::alloc(cs.ns(|| "alloc_circuit_vk"), || Ok(self.vk.as_ref().unwrap()))?;
        let proof = ProofVar::alloc(cs.ns(|| "alloc proof"), || Ok(self.proof.as_ref().unwrap()))?;
        let input: Vec<NonNativeFieldVar<Fr, Fq>> = self
            .input
            .as_ref()
            .map(|input| {
                input
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        NonNativeFieldVar::alloc_input(cs.ns(|| format!("alloc_input_{}", i)), || Ok(x)).unwrap()
                    })
                    .collect()
            })
            .ok_or(SynthesisError::AssignmentMissing)?;
        MarlinVerificationGadget::<Fr, Fq, PC, PCGadget>::verify::<_, FS, FSG>(
            cs.ns(|| "marlin_verification"),
            &vk,
            &input,
            &proof,
        )
        .unwrap()
        .enforce_equal(cs.ns(|| "enforce_equal"), &Boolean::Constant(true))?;
        Ok(())
    }
}

type PC = SonicKZG10<Bls12_377>;
type PCGadget = SonicKZG10Gadget<Bls12_377, BW6_761, Bls12_377PairingGadget>;

type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>;
type FSG = FiatShamirAlgebraicSpongeRngVar<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>;

type MarlinInst = MarlinCore<Fr, Fq, PC, FS, MarlinRecursiveMode>;

/// Run the multiple marlin program test.
#[test]
fn verifier_on_groth16() {
    let rng = &mut test_rng();
    let max_degree = snarkvm_marlin::ahp::AHPForR1CS::<Fr>::max_degree(10000, 25, 10000).unwrap();
    let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

    let (vk1, input1, proof1) = {
        // MulCircuit
        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = a * &b;

        let circ = MulCircuit {
            a: Some(a),
            b: Some(b),
            c: Some(c),
        };
        let (ipk, ivk) = MarlinInst::circuit_setup(&universal_srs, &circ).unwrap();
        let proof = MarlinInst::prove(&ipk, &circ, rng).unwrap();
        let input = vec![a, b, c];
        assert!(MarlinInst::verify(&ivk, &input, &proof).unwrap());
        let mut cs = TestConstraintSystem::new();
        let circ = RecursiveCircuit {
            vk: Some(ivk.clone()),
            proof: Some(proof.clone()),
            input: Some(input.clone()),
        };
        circ.generate_constraints(&mut cs).unwrap();
        assert!(cs.is_satisfied());
        (ivk, input, proof)
    };
    let (vk2, input2, proof2) = {
        // MulSquareCircuit
        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = (a * &b).square();

        let circ = MulSquareCircuit {
            a: Some(a),
            b: Some(b),
            c: Some(c),
        };

        let (ipk, ivk) = MarlinInst::circuit_setup(&universal_srs, &circ).unwrap();
        let proof = MarlinInst::prove(&ipk, &circ, rng).unwrap();
        let input = vec![a, b, c];
        assert!(MarlinInst::verify(&ivk, &input, &proof).unwrap());
        let mut cs = TestConstraintSystem::new();
        let circ = RecursiveCircuit {
            vk: Some(ivk.clone()),
            proof: Some(proof.clone()),
            input: Some(input.clone()),
        };
        circ.generate_constraints(&mut cs).unwrap();
        assert!(cs.is_satisfied());
        (ivk, input, proof)
    };

    let circ1 = RecursiveCircuit {
        vk: Some(vk1),
        proof: Some(proof1),
        input: Some(input1.clone()),
    };

    let circ2 = RecursiveCircuit {
        vk: Some(vk2.clone()),
        proof: Some(proof2.clone()),
        input: Some(input2.clone()),
    };

    println!("\n\nDiffing constraints now\n\n");
    circ1.diff(&circ2);

    let (rec_pk1, rec_vk1) = Groth16::<BW6_761, Vec<Fq>>::setup(&circ1, &mut SRS::CircuitSpecific(rng)).unwrap();
    let rec_input1 = circ1.public_input();
    let rec_proof1 = Groth16::<_, Vec<Fq>>::prove(&rec_pk1, &circ1, rng).unwrap();
    assert!(Groth16::verify(&rec_vk1, &rec_input1, &rec_proof1).unwrap());

    let rec_input2 = circ2.public_input();
    {
        let (rec_pk2, rec_vk2) = Groth16::<BW6_761, Vec<Fq>>::setup(&circ2, &mut SRS::CircuitSpecific(rng)).unwrap();
        let rec_proof2 = Groth16::<_, Vec<Fq>>::prove(&rec_pk2, &circ2, rng).unwrap();
        assert!(Groth16::verify(&rec_vk2, &rec_input2, &rec_proof2).unwrap());
    }
    let rec_proof2 = Groth16::<_, Vec<Fq>>::prove(&rec_pk1, &circ2, rng).unwrap();
    assert!(Groth16::verify(&rec_vk1, &rec_input2, &rec_proof2).unwrap());

    let circ3 = RecursiveCircuit {
        vk: Some(vk2.clone()),
        proof: Some(proof2.clone()),
        input: Some(input1.clone()),
    };
    let rec_input3 = circ2.public_input();
    let rec_proof3 = Groth16::<_, Vec<Fq>>::prove(&rec_pk1, &circ3, rng).unwrap();
    assert!(!Groth16::verify(&rec_vk1, &rec_input3, &rec_proof3).unwrap());
}
