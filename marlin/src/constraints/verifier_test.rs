#[cfg(test)]
mod tests {
    #![allow(unused_imports)]

    use crate::{
        ahp::prover::ProverMessage,
        constraints::{
            data_structures::{CircuitVerifyingKeyVar, ProofVar, ProverMessageVar},
            snark::{MarlinBound, MarlinSNARK},
            verifier::MarlinVerificationGadget,
        },
        fiat_shamir::{
            constraints::FiatShamirAlgebraicSpongeRngVar,
            poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
            FiatShamirAlgebraicSpongeRng,
        },
        marlin::{MarlinCore, MarlinRecursiveConfig, Proof},
    };

    use snarkvm_algorithms::{fft::DensePolynomial, traits::SNARK};
    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq, Fr},
        bw6_761::BW6_761,
        traits::PairingEngine,
    };
    use snarkvm_fields::Field;
    use snarkvm_gadgets::{
        curves::bls12_377::PairingGadget as Bls12PairingGadget,
        traits::curves::PairingGadget,
        utilities::{alloc::AllocGadget, boolean::Boolean, eq::EqGadget},
    };
    use snarkvm_nonnative::NonNativeFieldVar;
    use snarkvm_polycommit::marlin_pc::{BatchLCProofVar, CommitmentVar, MarlinKZG10, MarlinKZG10Gadget};
    use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, TestConstraintSystem};
    use snarkvm_utilities::UniformRand;

    use blake2::Blake2s;
    use core::ops::MulAssign;
    use hashbrown::HashMap;
    use rand::SeedableRng;

    type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>;
    type MultiPC = MarlinKZG10<Bls12_377>;

    type MarlinNativeInst = MarlinSNARK<Fr, Fq, MultiPC, FS, MarlinRecursiveConfig, Circuit<Fr>>;
    type MarlinNativeInstCore = MarlinCore<Fr, MultiPC, MarlinRecursiveConfig, Blake2s>;

    type MultiPCVar = MarlinKZG10Gadget<Bls12_377, BW6_761, Bls12PairingGadget>;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_variables: usize,
    }

    impl<F: Field> ConstraintSynthesizer<F> for Circuit<F> {
        fn generate_constraints<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| "alloc_a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "alloc_b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.alloc_input(
                || "alloc_input_c",
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    a.mul_assign(&b);
                    Ok(a)
                },
            )?;

            for i in 0..(self.num_variables - 3) {
                let _ = cs.alloc(
                    || format!("alloc_a_{}", i),
                    || self.a.ok_or(SynthesisError::AssignmentMissing),
                )?;
            }

            for i in 0..self.num_constraints {
                cs.enforce(
                    || format!("enforce_constraint_{}", i),
                    |lc| lc + a,
                    |lc| lc + b,
                    |lc| lc + c,
                );
            }
            Ok(())
        }
    }

    #[test]
    fn verifier_test() {
        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(123456789u64);

        let universal_srs = MarlinNativeInstCore::universal_setup(10000, 25, 10000, rng).unwrap();

        let num_constraints = 10000;
        let num_variables = 25;

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let mut c = a.clone();
        c.mul_assign(&b);

        let circ = Circuit {
            a: Some(a.clone()),
            b: Some(b),
            num_constraints,
            num_variables,
        };

        let (index_pk, index_vk) = MarlinNativeInstCore::circuit_setup(&universal_srs, &circ).unwrap();
        println!("Called index");

        // TODO (raychu86): Fix this error (Missing shifted randomness because of degree bounds).
        let proof = MarlinNativeInstCore::prove(&index_pk, &circ, rng).unwrap();
        println!("Called prover");

        assert!(MarlinNativeInstCore::verify(&index_vk, &[c], &proof).unwrap());
        println!("Called verifier");
        println!("\nShould not verify (i.e. verifier messages should print below):");
        assert!(!MarlinNativeInstCore::verify(&index_vk, &[a], &proof).unwrap());

        // Native works; now convert to the constraint world!

        let mut cs = TestConstraintSystem::<Fq>::new();

        // cs.set_optimization_goal(OptimizationGoal::Weight);

        // BEGIN: ivk to ivk_gadget
        let ivk_gadget: CircuitVerifyingKeyVar<Fr, Fq, MultiPC, MultiPCVar> =
            CircuitVerifyingKeyVar::alloc(cs.ns(|| "alloc#index vk"), || Ok(index_vk)).unwrap();
        // END: ivk to ivk_gadget

        // BEGIN: public input to public_input_gadget
        let public_input: Vec<Fr> = vec![c];

        let public_input_gadget: Vec<NonNativeFieldVar<Fr, Fq>> = public_input
            .iter()
            .enumerate()
            .map(|(i, x)| {
                NonNativeFieldVar::alloc_input(cs.ns(|| format!("alloc#public input {}", i)), || Ok(x)).unwrap()
            })
            .collect();
        // END: public input to public_input_gadget

        // BEGIN: proof to proof_gadget
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = proof;

        let commitment_gadgets: Vec<Vec<CommitmentVar<Bls12_377, BW6_761, Bls12PairingGadget>>> = commitments
            .iter()
            .enumerate()
            .map(|(i, lst)| {
                lst.iter()
                    .enumerate()
                    .map(|(j, comm)| {
                        CommitmentVar::alloc(cs.ns(|| format!("alloc#commitment_{}_{}", i, j)), || Ok(comm)).unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<Fr, Fq>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc#evaluation_{}", i)), || Ok(eval)).unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMessageVar<Fr, Fq>> = prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldVar<Fr, Fq>> = match msg.field_elements.is_empty() {
                    true => Vec::new(),
                    false => msg
                        .field_elements
                        .iter()
                        .map(|elem| {
                            NonNativeFieldVar::alloc(cs.ns(|| format!("alloc#prover message_{}", i)), || Ok(elem))
                                .unwrap()
                        })
                        .collect(),
                };

                ProverMessageVar { field_elements }
            })
            .collect();

        let pc_batch_proof =
            BatchLCProofVar::<Bls12_377, BW6_761, Bls12PairingGadget>::alloc(cs.ns(|| "alloc#proof"), || Ok(pc_proof))
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

        let proof_gadget: ProofVar<Fr, Fq, MultiPC, MultiPCVar> = ProofVar {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        };
        // END: proof to proof_gadget

        MarlinVerificationGadget::<Fr, Fq, MultiPC, MultiPCVar>::verify::<
            _,
            FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>,
            FiatShamirAlgebraicSpongeRngVar<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>,
        >(
            cs.ns(|| "marlin_verification"),
            &ivk_gadget,
            &public_input_gadget,
            &proof_gadget,
        )
        .unwrap()
        .enforce_equal(cs.ns(|| "enforce_equal"), &Boolean::Constant(true))
        .unwrap();

        println!("after Marlin, num_of_constraints = {}", cs.num_constraints());

        assert!(
            cs.is_satisfied(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap()
        );
    }
}
