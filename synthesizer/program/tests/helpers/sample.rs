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

use circuit::{AleoV0, Assignment, Circuit, Environment, Field, Inject, Mode};
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
use synthesizer_snark::{ProvingKey, UniversalSRS, VerifyingKey};

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

/// Compute `base`^`exponent` - 1`, in a purposefully constraint-inefficient manner for testing.
pub fn create_example_circuit<E: circuit::Environment>(
    base: console::types::Field<E::Network>,
    exponent: u64,
) -> Field<E> {
    let one = console::types::Field::<E::Network>::one();
    let two = one + one;

    // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    let mut candidate = Field::<E>::new(Mode::Public, one);
    let mut accumulator = Field::new(Mode::Private, base);
    for _ in 0..exponent {
        candidate += &accumulator;
        accumulator *= Field::new(Mode::Private, two);
    }

    assert_eq!(2, E::num_public());
    assert_eq!(2 * exponent + 1, E::num_private());
    assert_eq!(exponent, E::num_constraints());

    candidate
}

/// Returns a sample assignment for the example circuit.
pub fn sample_assignment(
    base: console::types::Field<<Circuit as Environment>::Network>,
    exponent: u64,
) -> Assignment<<Circuit as circuit::Environment>::BaseField> {
    let _candidate_output = create_example_circuit::<Circuit>(base, exponent);
    let assignment = Circuit::eject_assignment_and_reset();
    assert_eq!(0, Circuit::num_constants());
    assert_eq!(1, Circuit::num_public());
    assert_eq!(0, Circuit::num_private());
    assert_eq!(0, Circuit::num_constraints());
    assignment
}

/// Returns the sample circuit keys for the example circuit.
pub fn sample_keys(parameters: &[u64]) -> Vec<(ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)> {
    parameters
        .iter()
        .map(|i| {
            let assignment = sample_assignment(console::types::Field::zero(), *i);
            let srs = UniversalSRS::load().unwrap();
            let (proving_key, verifying_key) = srs.to_circuit_key("test", &assignment).unwrap();
            (proving_key, verifying_key)
        })
        .collect()
}
