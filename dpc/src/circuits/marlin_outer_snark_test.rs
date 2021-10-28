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
    prelude::*,
    testnet2::Testnet2,
    Execution,
    Function,
    FunctionType,
    InnerCircuit,
    InnerPrivateVariables,
    InnerPublicVariables,
    Network,
    Noop,
    OuterCircuit,
    OuterPrivateVariables,
    OuterPublicVariables,
    Program,
    ProgramPrivateVariables,
    ProgramPublicVariables,
    SynthesizedCircuit,
};

use snarkvm_algorithms::{traits::MerkleParameters, CRH, SNARK, SRS};
use snarkvm_gadgets::{
    integers::uint::UInt8,
    traits::{algorithms::CRHGadget, alloc::AllocGadget},
};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError, TestConstraintSystem};
use snarkvm_utilities::{FromBytes, ToMinimalBits};

use anyhow::Result;
use rand::{thread_rng, CryptoRng, Rng};
use std::sync::Arc;

#[derive(Clone, Debug)]
struct NewCircuit {
    pub(crate) function_id: <Testnet2 as Network>::FunctionID,
    pub(crate) proving_key: <<Testnet2 as Network>::ProgramSNARK as SNARK>::ProvingKey,
    pub(crate) verifying_key: <<Testnet2 as Network>::ProgramSNARK as SNARK>::VerifyingKey,
}

impl NewCircuit {
    /// Initializes a new instance of the mint program.
    fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        let public = ProgramPublicVariables::<Testnet2>::default();
        let (proving_key, verifying_key) = <<Testnet2 as Network>::ProgramSNARK as SNARK>::setup(
            &NewCircuitLogic::blank(&public),
            &mut *Testnet2::program_srs::<R>(rng).borrow_mut(),
        )?;
        Ok(Self {
            function_id: <Testnet2 as Network>::function_id(&verifying_key)?,
            proving_key,
            verifying_key,
        })
    }
}

impl Function<Testnet2> for NewCircuit {
    /// Returns the function ID.
    fn function_id(&self) -> <Testnet2 as Network>::FunctionID {
        self.function_id.clone()
    }

    /// Returns the circuit type.
    fn function_type(&self) -> FunctionType {
        FunctionType::Noop
    }

    /// Synthesizes the circuit inside the given constraint system.
    fn synthesize<CS: ConstraintSystem<<Testnet2 as Network>::InnerScalarField>>(
        &self,
        cs: &mut CS,
        public: &ProgramPublicVariables<Testnet2>,
    ) -> Result<(), SynthesisError> {
        NewCircuitLogic::blank(public).generate_constraints(cs)?;
        Ok(())
    }

    /// Executes the function, returning an proof.
    fn execute(
        &self,
        public: ProgramPublicVariables<Testnet2>,
        _private: &dyn ProgramPrivateVariables<Testnet2>,
    ) -> Result<<Testnet2 as Network>::ProgramProof> {
        let circuit = NewCircuitLogic::new(&public);
        let proof =
            <<Testnet2 as Network>::ProgramSNARK as SNARK>::prove(&self.proving_key, &circuit, &mut thread_rng())?;
        assert!(self.verify(&public, &proof));
        Ok(proof)
    }

    /// Returns true if the execution of the function is valid.
    fn verify(&self, public: &ProgramPublicVariables<Testnet2>, proof: &<Testnet2 as Network>::ProgramProof) -> bool {
        <<Testnet2 as Network>::ProgramSNARK as SNARK>::verify(&self.verifying_key, public, proof)
            .expect("Failed to verify proof")
    }
}

#[derive(Clone)]
struct NewCircuitLogic {
    pub(crate) public: ProgramPublicVariables<Testnet2>,
}

impl NewCircuitLogic {
    fn new(public: &ProgramPublicVariables<Testnet2>) -> Self {
        Self { public: public.clone() }
    }

    fn blank(public: &ProgramPublicVariables<Testnet2>) -> Self {
        Self { public: public.clone() }
    }
}

impl ConstraintSynthesizer<<Testnet2 as Network>::InnerScalarField> for NewCircuitLogic {
    fn generate_constraints<CS: ConstraintSystem<<Testnet2 as Network>::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let _position = UInt8::alloc_input_vec_le(cs.ns(|| "Alloc position"), &[0u8])?;

        let _transition_id_crh = <Testnet2 as Network>::TransitionIDCRHGadget::alloc_constant(
            &mut cs.ns(|| "Declare the transition ID CRH scheme"),
            || Ok(Testnet2::transition_id_parameters().crh()),
        )?;

        let _transition_id =
            <<Testnet2 as Network>::TransitionIDCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
                cs.ns(|| "Alloc the transition ID"),
                || Ok(self.public.transition_id),
            )?;

        let _alloc_num = UInt8::alloc(cs.ns(|| "Alloc random variable"), || Ok(0u8))?;

        Ok(())
    }
}

/// Run the multiple marlin program test.
fn testnet2_marlin_outer_multiple_functions_test() -> Result<()> {
    use snarkvm_parameters::testnet2::{
        InnerProvingKeyBytes,
        InnerVerifyingKeyBytes,
        NoopProvingKeyBytes,
        NoopVerifyingKeyBytes,
    };

    println!("\nSetup outer parameters\n");

    let rng = &mut thread_rng();

    // Load inner.
    let inner_proving_key = <<Testnet2 as Network>::InnerSNARK as SNARK>::ProvingKey::read_le(
        InnerProvingKeyBytes::load_bytes()?.as_slice(),
    )?;
    let inner_verifying_key = <<Testnet2 as Network>::InnerSNARK as SNARK>::VerifyingKey::read_le(
        InnerVerifyingKeyBytes::load_bytes()?.as_slice(),
    )?;
    let inner_proof =
        <Testnet2 as Network>::InnerSNARK::prove(&inner_proving_key, &InnerCircuit::<Testnet2>::blank(), rng)?;

    // Load noop program.
    let program_proving_key = <<Testnet2 as Network>::ProgramSNARK as SNARK>::ProvingKey::read_le(
        NoopProvingKeyBytes::load_bytes()?.as_slice(),
    )?;
    let program_verifying_key = <<Testnet2 as Network>::ProgramSNARK as SNARK>::VerifyingKey::read_le(
        NoopVerifyingKeyBytes::load_bytes()?.as_slice(),
    )?;

    let program = Program::<Testnet2>::new(vec![Arc::new(Noop::<Testnet2>::new())]).unwrap();
    let program_id = program.program_id();
    let program_path = program
        .to_program_path(&Testnet2::function_id(&program_verifying_key).unwrap())
        .unwrap();

    let proof = <<Testnet2 as Network>::ProgramSNARK as SNARK>::prove(
        &program_proving_key,
        &SynthesizedCircuit::<Testnet2>::Noop(ProgramPublicVariables::blank()),
        rng,
    )?;

    let outer_circuit = OuterCircuit::<Testnet2>::blank(inner_verifying_key.clone(), inner_proof, Execution {
        program_id,
        program_path,
        verifying_key: program_verifying_key.clone(),
        proof,
    });

    // Generate the outer snark parameters.
    let (outer_proving_key, outer_verifying_key) =
        <Testnet2 as Network>::OuterSNARK::setup(&outer_circuit, &mut SRS::CircuitSpecific(&mut thread_rng()))?;

    ///////////// START TEST with initial executor

    {
        println!("\nRunning outer proof with single function in program tree\n");

        let recipient = Account::new(rng);
        let amount = AleoAmount::ZERO;
        let request = Request::new_coinbase(recipient.address(), amount, rng).unwrap();
        let response = ResponseBuilder::new()
            .add_request(request.clone())
            .add_output(Output::new(recipient.address(), amount, Default::default(), None).unwrap())
            .build(rng)
            .unwrap();

        //////////////////////////////////////////////////////////////////////////

        // Fetch the ledger root, serial numbers, and program ID.
        let ledger_root = LedgerTree::<Testnet2>::new().unwrap().root();
        let serial_numbers = request.to_serial_numbers().unwrap();
        let program_id = request.to_program_id().unwrap();

        // Fetch the commitments and ciphertexts.
        let commitments = response.commitments();
        let ciphertexts = response.ciphertexts().clone();

        // Compute the local transitions root.
        let local_transitions_root = Transitions::<Testnet2>::new().unwrap().root();

        // Compute the transition ID.
        let transition_id =
            Transition::compute_transition_id(&serial_numbers, &commitments, &ciphertexts, AleoAmount::ZERO).unwrap();

        //////////////////////////////////////////////////////////////////////////

        // Compute the noop execution
        let execution = Execution {
            program_id: *Testnet2::noop_program_id(),
            program_path: Testnet2::noop_program_path().clone(),
            verifying_key: Testnet2::noop_circuit_verifying_key().clone(),
            proof: Noop::<Testnet2>::new()
                .execute(
                    ProgramPublicVariables::new(transition_id),
                    &NoopPrivateVariables::<Testnet2>::new_blank().unwrap(),
                )
                .unwrap(),
        };

        // Construct the inner circuit public and private variables.
        let inner_public =
            InnerPublicVariables::new(transition_id, ledger_root, local_transitions_root, Some(program_id));
        let inner_private = InnerPrivateVariables::new(&request, &response).unwrap();

        // Check that the core check constraint system was satisfied.
        let mut inner_cs = TestConstraintSystem::<<Testnet2 as Network>::InnerScalarField>::new();

        let inner_circuit = InnerCircuit::new(inner_public.clone(), inner_private);
        inner_circuit
            .generate_constraints(&mut inner_cs.ns(|| "Inner circuit"))
            .unwrap();

        assert!(inner_cs.is_satisfied());

        // NOTE: Do not change this to `Testnet2::inner_circuit_id()` as that will load the *saved* inner circuit VK.
        let inner_circuit_id = <Testnet2 as Network>::inner_circuit_id_crh()
            .hash_bits(&inner_verifying_key.to_minimal_bits())
            .unwrap();

        let inner_proof = <Testnet2 as Network>::InnerSNARK::prove(&inner_proving_key, &inner_circuit, rng).unwrap();

        // Verify that the inner circuit proof passes.
        assert!(<Testnet2 as Network>::InnerSNARK::verify(&inner_verifying_key, &inner_public, &inner_proof).unwrap());

        // Construct the outer circuit public and private variables.
        let outer_public = OuterPublicVariables::new(
            transition_id,
            ledger_root,
            local_transitions_root,
            inner_circuit_id.clone(),
        );
        let outer_private = OuterPrivateVariables::new(inner_verifying_key.clone(), inner_proof, execution);

        // Check that the proof check constraint system was satisfied.
        let mut outer_cs = TestConstraintSystem::<<Testnet2 as Network>::OuterScalarField>::new();

        let outer_circuit = OuterCircuit::new(outer_public.clone(), outer_private);
        outer_circuit
            .generate_constraints(&mut outer_cs.ns(|| "Outer circuit"))
            .unwrap();

        if !outer_cs.is_satisfied() {
            println!("=========================================================");
            println!("Unsatisfied constraints:\n{}", outer_cs.which_is_unsatisfied().unwrap());
            println!("=========================================================");
        }

        // Verify that the outer proof verifies

        let outer_proof = <Testnet2 as Network>::OuterSNARK::prove(&outer_proving_key, &outer_circuit, rng).unwrap();

        // Verify that the outer circuit proof passes.
        assert!(<Testnet2 as Network>::OuterSNARK::verify(&outer_verifying_key, &outer_public, &outer_proof).unwrap());

        //////////////////////////////////////////////

        // START TESTING NEW MARLIN FUNCTIONS IN THE PROGRAM

        //////////////////////////////////////////////

        println!("\nRunning outer proof with a new function in program tree\n");

        // Craft a new circuit and setup parameters.
        let new_circuit = NewCircuit::setup(&mut thread_rng()).unwrap();

        // Create a new program
        let new_program =
            Program::<Testnet2>::new(vec![Arc::new(Noop::<Testnet2>::new()), Arc::new(new_circuit.clone())]).unwrap();
        let new_program_id = new_program.program_id();
        let new_program_path = new_program
            .to_program_path(&Testnet2::function_id(&new_circuit.verifying_key).unwrap())
            .unwrap();

        let new_proof = <<Testnet2 as Network>::ProgramSNARK as SNARK>::prove(
            &new_circuit.proving_key,
            &NewCircuitLogic::new(&ProgramPublicVariables::blank()),
            rng,
        )?;

        println!("Generating new proof");

        let new_execution = Execution {
            program_id: new_program_id,
            program_path: new_program_path,
            verifying_key: new_circuit.verifying_key.clone(),
            proof: new_proof,
        };

        // Construct the inner circuit public and private variables.
        let inner_public =
            InnerPublicVariables::new(transition_id, ledger_root, local_transitions_root, Some(program_id));
        let inner_private = InnerPrivateVariables::new(&request, &response).unwrap();

        // Check that the core check constraint system was satisfied.
        let mut new_inner_cs = TestConstraintSystem::<<Testnet2 as Network>::InnerScalarField>::new();

        let inner_circuit = InnerCircuit::new(inner_public.clone(), inner_private);
        inner_circuit
            .generate_constraints(&mut new_inner_cs.ns(|| "New Inner circuit"))
            .unwrap();

        assert!(new_inner_cs.is_satisfied());

        let inner_proof = <Testnet2 as Network>::InnerSNARK::prove(&inner_proving_key, &inner_circuit, rng).unwrap();

        // Verify that the inner circuit proof passes.
        assert!(<Testnet2 as Network>::InnerSNARK::verify(&inner_verifying_key, &inner_public, &inner_proof).unwrap());

        // Construct the outer circuit public and private variables.
        let new_outer_public =
            OuterPublicVariables::new(transition_id, ledger_root, local_transitions_root, inner_circuit_id);
        let new_outer_private = OuterPrivateVariables::new(inner_verifying_key.clone(), inner_proof, new_execution);

        // Check that the proof check constraint system was satisfied.
        let mut new_outer_cs = TestConstraintSystem::<<Testnet2 as Network>::OuterScalarField>::new();

        let new_outer_circuit = OuterCircuit::new(new_outer_public.clone(), new_outer_private);
        new_outer_circuit
            .generate_constraints(&mut new_outer_cs.ns(|| "New Outer circuit"))
            .unwrap();

        if !new_outer_cs.is_satisfied() {
            println!("=========================================================");
            println!(
                "Unsatisfied constraints:\n{}",
                new_outer_cs.which_is_unsatisfied().unwrap()
            );
            println!("=========================================================");
        }
        assert!(new_outer_cs.is_satisfied());

        // Verify that the outer proof verifies

        let new_outer_proof =
            <Testnet2 as Network>::OuterSNARK::prove(&outer_proving_key, &new_outer_circuit, rng).unwrap();

        // Verify that the new outer circuit proof passes.
        assert!(
            <Testnet2 as Network>::OuterSNARK::verify(&outer_verifying_key, &new_outer_public, &new_outer_proof)
                .unwrap()
        );
    }

    Ok(())
}

#[test]
fn test_testnet2_marlin_outer_multiple_functions() {
    testnet2_marlin_outer_multiple_functions_test().unwrap();
}
