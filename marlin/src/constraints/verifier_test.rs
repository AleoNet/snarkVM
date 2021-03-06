#[cfg(test)]
mod tests {
    use crate::ahp::prover::ProverMsg;
    use crate::{
        constraints::{
            data_structures::{IndexVerifierKeyVar, ProofVar, ProverMsgVar},
            verifier::Marlin,
        },
        fiat_shamir::{
            constraints::FiatShamirAlgebraicSpongeRngVar, poseidon::constraints::PoseidonSpongeVar,
            poseidon::PoseidonSponge, FiatShamirAlgebraicSpongeRng,
        },
        Marlin as MarlinNative, MarlinRecursiveConfig, Proof,
    };
    use ark_ec::{CurveCycle, PairingEngine, PairingFriendlyCycle};
    use ark_ff::{Field, UniformRand};
    use ark_mnt4_298::{constraints::PairingVar as MNT4PairingVar, Fq, Fr, MNT4_298};
    use ark_mnt6_298::MNT6_298;
    use ark_nonnative_field::NonNativeFieldVar;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly_commit::marlin_pc::{
        BatchLCProofVar, CommitmentVar, MarlinKZG10, MarlinKZG10Gadget,
    };
    use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
    use ark_relations::r1cs::OptimizationGoal;
    use ark_relations::{
        lc, ns,
        r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError},
    };
    use core::ops::MulAssign;
    use hashbrown::HashMap;

    #[derive(Copy, Clone, Debug)]
    struct MNT298Cycle;
    impl CurveCycle for MNT298Cycle {
        type E1 = <MNT6_298 as PairingEngine>::G1Affine;
        type E2 = <MNT4_298 as PairingEngine>::G1Affine;
    }
    impl PairingFriendlyCycle for MNT298Cycle {
        type Engine1 = MNT6_298;
        type Engine2 = MNT4_298;
    }

    type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>;
    type MultiPC = MarlinKZG10<MNT4_298, DensePolynomial<Fr>>;
    type MarlinNativeInst = MarlinNative<Fr, Fq, MultiPC, FS, MarlinRecursiveConfig>;

    type MultiPCVar = MarlinKZG10Gadget<MNT298Cycle, DensePolynomial<Fr>, MNT4PairingVar>;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_variables: usize,
    }

    impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<ConstraintF>,
        ) -> Result<(), SynthesisError> {
            let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.new_input_variable(|| {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                Ok(a)
            })?;

            for _ in 0..(self.num_variables - 3) {
                let _ =
                    cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
            }

            for _ in 0..self.num_constraints {
                cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
            }
            Ok(())
        }
    }

    #[test]
    fn verifier_test() {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinNativeInst::universal_setup(10000, 25, 10000, rng).unwrap();

        let num_constraints = 10000;
        let num_variables = 25;

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let mut c = a;
        c.mul_assign(&b);

        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints,
            num_variables,
        };

        let (index_pk, index_vk) = MarlinNativeInst::index(&universal_srs, circ).unwrap();
        println!("Called index");

        let proof = MarlinNativeInst::prove(&index_pk, circ, rng).unwrap();
        println!("Called prover");

        assert!(MarlinNativeInst::verify(&index_vk, &[c], &proof).unwrap());
        println!("Called verifier");
        println!("\nShould not verify (i.e. verifier messages should print below):");
        assert!(!MarlinNativeInst::verify(&index_vk, &[a], &proof).unwrap());

        // Native works; now convert to the constraint world!

        let cs_sys = ConstraintSystem::<Fq>::new();
        let cs = ConstraintSystemRef::new(cs_sys);
        cs.set_optimization_goal(OptimizationGoal::Weight);

        // BEGIN: ivk to ivk_gadget
        let ivk_gadget: IndexVerifierKeyVar<Fr, Fq, MultiPC, MultiPCVar> =
            IndexVerifierKeyVar::new_witness(ns!(cs, "alloc#index vk"), || Ok(index_vk)).unwrap();
        // END: ivk to ivk_gadget

        // BEGIN: public input to public_input_gadget
        let public_input: Vec<Fr> = vec![c];

        let public_input_gadget: Vec<NonNativeFieldVar<Fr, Fq>> = public_input
            .iter()
            .map(|x| {
                NonNativeFieldVar::new_input(ns!(cs.clone(), "alloc#public input"), || Ok(x))
                    .unwrap()
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

        let commitment_gadgets: Vec<Vec<CommitmentVar<MNT298Cycle, MNT4PairingVar>>> = commitments
            .iter()
            .map(|lst| {
                lst.iter()
                    .map(|comm| {
                        CommitmentVar::new_witness(ns!(cs.clone(), "alloc#commitment"), || Ok(comm))
                            .unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<Fr, Fq>> = evaluations
            .iter()
            .map(|eval| {
                NonNativeFieldVar::new_witness(ns!(cs.clone(), "alloc#evaluation"), || Ok(eval))
                    .unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMsgVar<Fr, Fq>> = prover_messages
            .iter()
            .map(|msg| {
                let field_elements: Vec<NonNativeFieldVar<Fr, Fq>> = match msg.clone() {
                    ProverMsg::EmptyMessage => Vec::new(),
                    ProverMsg::FieldElements(v) => v
                        .iter()
                        .map(|elem| {
                            NonNativeFieldVar::new_witness(ns!(cs, "alloc#prover message"), || {
                                Ok(elem)
                            })
                            .unwrap()
                        })
                        .collect(),
                };

                ProverMsgVar { field_elements }
            })
            .collect();

        let pc_batch_proof =
            BatchLCProofVar::<MNT298Cycle, DensePolynomial<Fr>, MNT4PairingVar>::new_witness(
                ns!(cs, "alloc#proof"),
                || Ok(pc_proof),
            )
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
            cs: cs.clone(),
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        };
        // END: proof to proof_gadget

        Marlin::<Fr, Fq, MultiPC, MultiPCVar>::verify::<
            FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq>>,
            FiatShamirAlgebraicSpongeRngVar<Fr, Fq, PoseidonSponge<Fq>, PoseidonSpongeVar<Fq>>,
        >(&ivk_gadget, &public_input_gadget, &proof_gadget)
        .unwrap()
        .enforce_equal(&Boolean::Constant(true))
        .unwrap();

        println!(
            "after Marlin, num_of_constraints = {}",
            cs.num_constraints()
        );

        assert!(
            cs.is_satisfied().unwrap(),
            "Constraints not satisfied: {}",
            cs.which_is_unsatisfied().unwrap().unwrap_or_default()
        );
    }
}
