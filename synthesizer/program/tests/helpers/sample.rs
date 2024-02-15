// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use circuit::{prelude::One as CircuitOne, AleoV0, Assignment, Circuit, Eject, Environment, Field, Inject, Mode};
use console::{
    network::MainnetV0,
    prelude::{One, *},
    program::{Identifier, Literal, Plaintext, Register, Value},
};
use snarkvm_synthesizer_program::{
    traits::{RegistersStore, RegistersStoreCircuit},
    FinalizeGlobalState,
};
use synthesizer_process::{Authorization, CallStack, FinalizeRegisters, Registers, Stack, StackProgramTypes};
use synthesizer_snark::{Certificate, Proof, ProvingKey, UniversalSRS, VerifyingKey};

use once_cell::sync::OnceCell;

type CurrentNetwork = MainnetV0;
type CurrentAleo = AleoV0;

/// Samples the registers. Note: Do not replicate this for real program use, it is insecure.
pub fn sample_registers(
    stack: &Stack<CurrentNetwork>,
    function_name: &Identifier<CurrentNetwork>,
    values: &[(&Literal<CurrentNetwork>, Option<circuit::Mode>)],
) -> Result<Registers<CurrentNetwork, CurrentAleo>> {
    // Initialize the registers.
    let mut registers = Registers::<CurrentNetwork, CurrentAleo>::new(
        CallStack::evaluate(Authorization::try_from((vec![], vec![]))?)?,
        stack.get_register_types(function_name)?.clone(),
    );

    // For each value, store the register and value.
    for (index, (literal, mode)) in values.iter().enumerate() {
        // Initialize the register.
        let register = Register::Locator(index as u64);
        // Initialize the console value.
        let value = Value::Plaintext(Plaintext::from(*literal));
        // Store the value in the console registers.
        registers.store(stack, &register, value.clone())?;
        // If the mode is not `None`,
        if let Some(mode) = mode {
            use circuit::Inject;

            // Initialize the circuit value.
            let circuit_value = circuit::Value::new(*mode, value);
            // Store the value in the circuit registers.
            registers.store_circuit(stack, &register, circuit_value)?;
        }
    }
    Ok(registers)
}

/// Samples the finalize registers. Note: Do not replicate this for real program use, it is insecure.
pub fn sample_finalize_registers(
    stack: &Stack<CurrentNetwork>,
    function_name: &Identifier<CurrentNetwork>,
    literals: &[&Literal<CurrentNetwork>],
) -> Result<FinalizeRegisters<CurrentNetwork>> {
    // Initialize the registers.
    let mut finalize_registers = FinalizeRegisters::<CurrentNetwork>::new(
        FinalizeGlobalState::from(1, 1, [0; 32]),
        <CurrentNetwork as Network>::TransitionID::default(),
        *function_name,
        stack.get_finalize_types(function_name)?.clone(),
    );

    // For each literal,
    for (index, literal) in literals.iter().enumerate() {
        // Initialize the register
        let register = Register::Locator(index as u64);
        // Initialize the console value.
        let value = Value::Plaintext(Plaintext::from(*literal));
        // Store the value in the console registers.
        finalize_registers.store(stack, &register, value)?;
    }

    Ok(finalize_registers)
}

/// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
fn create_example_circuit<E: circuit::Environment>() -> Field<E> {
    let one = console::types::Field::<E::Network>::one();
    let two = one + one;

    const EXPONENT: u64 = 64;

    // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    let mut candidate = Field::<E>::new(Mode::Public, one);
    let mut accumulator = Field::new(Mode::Private, two);
    for _ in 0..EXPONENT {
        candidate += &accumulator;
        accumulator *= Field::new(Mode::Private, two);
    }

    assert_eq!((accumulator - Field::one()).eject_value(), candidate.eject_value());
    assert_eq!(2, E::num_public());
    assert_eq!(2 * EXPONENT + 1, E::num_private());
    assert_eq!(EXPONENT, E::num_constraints());
    assert!(E::is_satisfied());

    candidate
}

/// Returns a sample assignment for the example circuit.
pub(crate) fn sample_assignment() -> Assignment<<Circuit as circuit::Environment>::BaseField> {
    static INSTANCE: OnceCell<Assignment<<Circuit as circuit::Environment>::BaseField>> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let _candidate_output = create_example_circuit::<Circuit>();
            let assignment = Circuit::eject_assignment_and_reset();
            assert_eq!(0, Circuit::num_constants());
            assert_eq!(1, Circuit::num_public());
            assert_eq!(0, Circuit::num_private());
            assert_eq!(0, Circuit::num_constraints());
            assignment
        })
        .clone()
}

/// Returns the sample circuit keys for the example circuit.
pub(crate) fn sample_keys() -> (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>) {
    static INSTANCE: OnceCell<(ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let assignment = sample_assignment();
            let srs = UniversalSRS::load().unwrap();
            let (proving_key, verifying_key) = srs.to_circuit_key("test", &assignment).unwrap();
            (proving_key, verifying_key)
        })
        .clone()
}

/// Returns a sample proof for the example circuit.
pub(crate) fn sample_proof() -> Proof<CurrentNetwork> {
    static INSTANCE: OnceCell<Proof<CurrentNetwork>> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let assignment = sample_assignment();
            let (proving_key, _) = sample_keys();
            proving_key.prove("test", &assignment, &mut TestRng::default()).unwrap()
        })
        .clone()
}

/// Returns a sample certificate for the example circuit.
pub(super) fn sample_certificate() -> Certificate<CurrentNetwork> {
    static INSTANCE: OnceCell<Certificate<CurrentNetwork>> = OnceCell::new();
    INSTANCE
        .get_or_init(|| {
            let (proving_key, verifying_key) = sample_keys();
            // Return the certificate.
            Certificate::certify("test", &proving_key, &verifying_key).unwrap()
        })
        .clone()
}
