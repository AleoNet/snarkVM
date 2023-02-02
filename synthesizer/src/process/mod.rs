// Copyright (C) 2019-2022 Aleo Systems Inc.
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

mod stack;
pub use stack::*;

mod authorize;
mod deploy;
mod evaluate;
mod execute;
mod execute_fee;

use crate::{
    block::{Input, Transition},
    program::{Instruction, Operand, Program},
    snark::{ProvingKey, UniversalSRS, VerifyingKey},
    store::{ProgramStorage, ProgramStore},
};
use console::{
    account::PrivateKey,
    network::prelude::*,
    program::{Identifier, Plaintext, ProgramID, Record, Request, Response, Value},
    types::{I64, U16, U64},
};

use aleo_std::prelude::{finish, lap, timer};
use indexmap::IndexMap;
use parking_lot::RwLock;
use std::sync::Arc;

#[cfg(test)]
use std::collections::HashMap;

#[cfg(feature = "aleo-cli")]
use colored::Colorize;

#[derive(Clone)]
pub struct Process<N: Network> {
    /// The universal SRS.
    universal_srs: Arc<UniversalSRS<N>>,
    /// The mapping of program IDs to stacks.
    stacks: IndexMap<ProgramID<N>, Stack<N>>,
}

impl<N: Network> Process<N> {
    /// Initializes a new process.
    #[inline]
    pub fn setup<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        let timer = timer!("Process:setup");

        // Initialize the process.
        let mut process = Self { universal_srs: Arc::new(UniversalSRS::load()?), stacks: IndexMap::new() };
        lap!(timer, "Initialize process");

        // Initialize the 'credits.aleo' program.
        let program = Program::credits()?;
        lap!(timer, "Load credits program");

        // Compute the 'credits.aleo' program stack.
        let stack = Stack::new(&process, &program)?;
        lap!(timer, "Initialize stack");

        // Synthesize the 'credits.aleo' circuit keys.
        for function_name in program.functions().keys() {
            stack.synthesize_key::<A, _>(function_name, rng)?;
            lap!(timer, "Synthesize circuit keys for {function_name}");
        }
        lap!(timer, "Synthesize credits program keys");

        // Add the 'credits.aleo' stack to the process.
        process.stacks.insert(*program.id(), stack);

        finish!(timer);
        // Return the process.
        Ok(process)
    }

    /// Adds a new program to the process.
    /// If you intend to `execute` the program, use `deploy` and `finalize_deployment` instead.
    #[inline]
    pub fn add_program(&mut self, program: &Program<N>) -> Result<()> {
        // Compute the program stack.
        let stack = Stack::new(self, program)?;
        // Add the stack to the process.
        self.stacks.insert(*program.id(), stack);
        // Return success.
        Ok(())
    }
}

impl<N: Network> Process<N> {
    /// Initializes a new process.
    #[inline]
    pub fn load() -> Result<Self> {
        let timer = timer!("Process::load");

        // Initialize the process.
        let mut process = Self { universal_srs: Arc::new(UniversalSRS::load()?), stacks: IndexMap::new() };
        lap!(timer, "Initialize process");

        // Initialize the 'credits.aleo' program.
        let program = Program::credits()?;
        lap!(timer, "Load credits program");

        // Compute the 'credits.aleo' program stack.
        let stack = Stack::new(&process, &program)?;
        lap!(timer, "Initialize stack");

        // Synthesize the 'credits.aleo' circuit keys.
        for function_name in program.functions().keys() {
            // Load the proving key.
            let proving_key = N::get_credits_proving_key(function_name.to_string())?;
            stack.insert_proving_key(function_name, ProvingKey::new(proving_key.clone()))?;
            lap!(timer, "Load proving key for {function_name}");

            // Load the verifying key.
            let verifying_key = N::get_credits_verifying_key(function_name.to_string())?;
            stack.insert_verifying_key(function_name, VerifyingKey::new(verifying_key.clone()))?;
            lap!(timer, "Load verifying key for {function_name}");
        }
        lap!(timer, "Load circuit keys");

        // Initialize the inclusion proving key.
        let _ = N::inclusion_proving_key();
        lap!(timer, "Load inclusion proving key");

        // Initialize the inclusion verifying key.
        let _ = N::inclusion_verifying_key();
        lap!(timer, "Load inclusion verifying key");

        // Add the stack to the process.
        process.stacks.insert(*program.id(), stack);

        finish!(timer, "Process::load");
        // Return the process.
        Ok(process)
    }

    /// Initializes a new process with a cache of previously used keys. This version is suitable for tests
    /// (which often use nested loops that keep reusing those), as their deserialization is slow.
    #[cfg(test)]
    #[inline]
    pub fn load_with_cache(cache: &mut HashMap<String, (ProvingKey<N>, VerifyingKey<N>)>) -> Result<Self> {
        // Initialize the process.
        let mut process = Self { universal_srs: Arc::new(UniversalSRS::load()?), stacks: IndexMap::new() };

        // Initialize the 'credits.aleo' program.
        let program = Program::credits()?;
        // Compute the 'credits.aleo' program stack.
        let stack = Stack::new(&process, &program)?;

        // Synthesize the 'credits.aleo' circuit keys.
        for function_name in program.functions().keys() {
            // Cache the proving and verifying key.
            let (proving_key, verifying_key) = cache.entry(function_name.to_string()).or_insert_with(|| {
                // Load the proving key.
                let proving_key = N::get_credits_proving_key(function_name.to_string()).unwrap();
                // Load the verifying key.
                let verifying_key = N::get_credits_verifying_key(function_name.to_string()).unwrap();

                (ProvingKey::new(proving_key.clone()), VerifyingKey::new(verifying_key.clone()))
            });
            // Insert the proving and verifying key.
            stack.insert_proving_key(function_name, proving_key.clone())?;
            stack.insert_verifying_key(function_name, verifying_key.clone())?;
        }

        // Add the stack to the process.
        process.stacks.insert(*program.id(), stack);
        // Return the process.
        Ok(process)
    }

    /// Returns the universal SRS.
    #[inline]
    pub const fn universal_srs(&self) -> &Arc<UniversalSRS<N>> {
        &self.universal_srs
    }

    /// Returns `true` if the process contains the program with the given ID.
    #[inline]
    pub fn contains_program(&self, program_id: &ProgramID<N>) -> bool {
        self.stacks.contains_key(program_id)
    }

    /// Returns the stack for the given program ID.
    #[inline]
    pub fn get_stack(&self, program_id: impl TryInto<ProgramID<N>>) -> Result<&Stack<N>> {
        // Prepare the program ID.
        let program_id = program_id.try_into().map_err(|_| anyhow!("Invalid program ID"))?;
        // Retrieve the stack.
        let stack = self.stacks.get(&program_id).ok_or_else(|| anyhow!("Program '{program_id}' does not exist"))?;
        // Ensure the program ID matches.
        ensure!(stack.program_id() == &program_id, "Expected program '{}', found '{program_id}'", stack.program_id());
        // Return the stack.
        Ok(stack)
    }

    /// Returns the program for the given program ID.
    #[inline]
    pub fn get_program(&self, program_id: impl TryInto<ProgramID<N>>) -> Result<&Program<N>> {
        self.get_stack(program_id).map(Stack::program)
    }

    /// Returns the proving key for the given program ID and function name.
    #[inline]
    pub fn get_proving_key(
        &self,
        program_id: impl TryInto<ProgramID<N>>,
        function_name: impl TryInto<Identifier<N>>,
    ) -> Result<ProvingKey<N>> {
        // Prepare the function name.
        let function_name = function_name.try_into().map_err(|_| anyhow!("Invalid function name"))?;
        // Return the proving key.
        self.get_stack(program_id)?.get_proving_key(&function_name)
    }

    /// Returns the verifying key for the given program ID and function name.
    #[inline]
    pub fn get_verifying_key(
        &self,
        program_id: impl TryInto<ProgramID<N>>,
        function_name: impl TryInto<Identifier<N>>,
    ) -> Result<VerifyingKey<N>> {
        // Prepare the function name.
        let function_name = function_name.try_into().map_err(|_| anyhow!("Invalid function name"))?;
        // Return the verifying key.
        self.get_stack(program_id)?.get_verifying_key(&function_name)
    }

    /// Inserts the given proving key, for the given program ID and function name.
    #[inline]
    pub fn insert_proving_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        proving_key: ProvingKey<N>,
    ) -> Result<()> {
        self.get_stack(program_id)?.insert_proving_key(function_name, proving_key)
    }

    /// Inserts the given verifying key, for the given program ID and function name.
    #[inline]
    pub fn insert_verifying_key(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        verifying_key: VerifyingKey<N>,
    ) -> Result<()> {
        self.get_stack(program_id)?.insert_verifying_key(function_name, verifying_key)
    }

    /// Synthesizes the proving and verifying key for the given program ID and function name.
    #[inline]
    pub fn synthesize_key<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        program_id: &ProgramID<N>,
        function_name: &Identifier<N>,
        rng: &mut R,
    ) -> Result<()> {
        // Synthesize the proving and verifying key.
        self.get_stack(program_id)?.synthesize_key::<A, R>(function_name, rng)
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{Process, Program, Transition};
    use console::{account::PrivateKey, network::Testnet3, program::Identifier};

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    pub(crate) fn sample_key() -> (Identifier<CurrentNetwork>, ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)
    {
        static INSTANCE: OnceCell<(
            Identifier<CurrentNetwork>,
            ProvingKey<CurrentNetwork>,
            VerifyingKey<CurrentNetwork>,
        )> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                let (string, program) = Program::<CurrentNetwork>::parse(
                    r"
program testing.aleo;

function compute:
    input r0 as u32.private;
    input r1 as u32.public;
    add r0 r1 into r2;
    output r2 as u32.public;",
                )
                .unwrap();
                assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

                // Declare the function name.
                let function_name = Identifier::from_str("compute").unwrap();

                // Initialize the RNG.
                let rng = &mut TestRng::default();

                // Construct the process.
                let process = sample_process(&program);

                // Synthesize a proving and verifying key.
                process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

                // Get the proving and verifying key.
                let proving_key = process.get_proving_key(program.id(), function_name).unwrap();
                let verifying_key = process.get_verifying_key(program.id(), function_name).unwrap();

                (function_name, proving_key, verifying_key)
            })
            .clone()
    }

    pub(crate) fn sample_execution() -> Execution<CurrentNetwork> {
        static INSTANCE: OnceCell<Execution<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                let (string, program) = Program::<CurrentNetwork>::parse(
                    r"
program testing.aleo;

function compute:
    input r0 as u32.private;
    input r1 as u32.public;
    add r0 r1 into r2;
    output r2 as u32.public;",
                )
                .unwrap();
                assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

                // Declare the function name.
                let function_name = Identifier::from_str("compute").unwrap();

                // Initialize the RNG.
                let rng = &mut TestRng::default();
                // Initialize a new caller account.
                let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

                // Construct the process.
                let process = sample_process(&program);
                // Authorize the function call.
                let authorization = process
                    .authorize::<CurrentAleo, _>(
                        &caller_private_key,
                        program.id(),
                        function_name,
                        ["5u32", "10u32"].into_iter(),
                        rng,
                    )
                    .unwrap();
                assert_eq!(authorization.len(), 1);
                // Execute the request.
                let (_response, execution, _inclusion, _metrics) =
                    process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
                assert_eq!(execution.len(), 1);
                // Return the execution.
                execution
            })
            .clone()
    }

    pub(crate) fn sample_transition() -> Transition<CurrentNetwork> {
        // Retrieve the execution.
        let mut execution = sample_execution();
        // Ensure the execution is not empty.
        assert!(!execution.is_empty());
        // Return the transition.
        execution.pop().unwrap()
    }

    /// Initializes a new process with the given program.
    pub(crate) fn sample_process(program: &Program<CurrentNetwork>) -> Process<CurrentNetwork> {
        // Construct a new process.
        let mut process = Process::load().unwrap();
        // Add the program to the process.
        process.add_program(program).unwrap();
        // Return the process.
        process
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ProgramMemory;
    use circuit::network::AleoV0;
    use console::{
        account::{Address, PrivateKey, ViewKey},
        network::Testnet3,
        program::{Identifier, Literal, Value},
        types::Field,
    };

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_process_execute_mint() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::credits().unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();
        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();
        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&format!("{caller}")).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("1_100_000_000_000_000_u64").unwrap();

        // Construct the process.
        let mut process = Process::load().unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                Identifier::from_str("mint").unwrap(),
                [r0.clone(), r1.clone()].iter(),
                rng,
            )
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(2)]).unwrap();
        let nonce = CurrentNetwork::g_scalar_multiply(&randomizer);

        // Declare the expected output value.
        let r2 = Value::from_str(&format!(
            "{{ owner: {caller}.private, gates: 1_100_000_000_000_000_u64.private, _nonce: {nonce}.public }}"
        ))
        .unwrap();

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(r2, candidate[0]);
        process.verify_execution::<true>(&execution).unwrap();

        // use circuit::Environment;
        //
        // assert_eq!(22152, CurrentAleo::num_constants());
        // assert_eq!(9, CurrentAleo::num_public());
        // assert_eq!(20561, CurrentAleo::num_private());
        // assert_eq!(20579, CurrentAleo::num_constraints());
        // assert_eq!(79386, CurrentAleo::num_gates());

        /******************************************/

        // Ensure a non-coinbase program function fails.

        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program token.aleo;

  record token:
    owner as address.private;
    gates as u64.private;

  function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 r1 into r2 as token.record;
    output r2 as token.record;",
        )
        .unwrap();
        process.add_program(&program).unwrap();

        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                Identifier::from_str("mint").unwrap(),
                [r0, r1].iter(),
                rng,
            )
            .unwrap();
        let result = process.execute::<CurrentAleo, _>(authorization, rng);
        assert!(result.is_err());
        assert_eq!(
            result.err().unwrap().to_string(),
            format!("'token.aleo/mint' is not satisfied on the given inputs (26610 constraints).")
        );
    }

    #[test]
    fn test_process_circuit_key() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r#"program testing.aleo;

function hello_world:
    input r0 as u32.public;
    input r1 as u32.private;
    add r0 r1 into r2;
    output r2 as u32.private;
"#,
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("hello_world").unwrap();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, &mut TestRng::default()).unwrap();
    }

    #[test]
    fn test_process_multirecords() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program multirecord.aleo;

  record record_a:
    owner as address.private;
    gates as u64.private;

  record record_b:
    owner as address.private;
    gates as u64.private;

  function initialize:
    input r0 as record_a.record;
    input r1 as record_b.record;
    cast r0.owner r0.gates into r2 as record_a.record;
    cast r1.owner r1.gates into r3 as record_b.record;
    output r2 as record_a.record;
    output r3 as record_b.record;",
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("initialize").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input_a =
            Value::from_str(&format!("{{ owner: {caller}.private, gates: 1234u64.private, _nonce: 0group.public }}"))
                .unwrap();
        let input_b =
            Value::from_str(&format!("{{ owner: {caller}.private, gates: 4321u64.private, _nonce: 0group.public }}"))
                .unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(
                &caller_private_key,
                program.id(),
                function_name,
                [input_a, input_b].iter(),
                rng,
            )
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer_a = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(2)]).unwrap();
        let nonce_a = CurrentNetwork::g_scalar_multiply(&randomizer_a);

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer_b = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(3)]).unwrap();
        let nonce_b = CurrentNetwork::g_scalar_multiply(&randomizer_b);

        // Declare the output value.
        let output_a = Value::from_str(&format!(
            "{{ owner: {caller}.private, gates: 1234u64.private, _nonce: {nonce_a}.public }}"
        ))
        .unwrap();
        let output_b = Value::from_str(&format!(
            "{{ owner: {caller}.private, gates: 4321u64.private, _nonce: {nonce_b}.public }}"
        ))
        .unwrap();

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(output_a, candidate[0]);
        assert_eq!(output_b, candidate[1]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(output_a, candidate[0]);
        assert_eq!(output_b, candidate[1]);

        process.verify_execution::<false>(&execution).unwrap();

        // use circuit::Environment;
        //
        // assert_eq!(20060, CurrentAleo::num_constants());
        // assert_eq!(12, CurrentAleo::num_public());
        // assert_eq!(57602, CurrentAleo::num_private());
        // assert_eq!(57684, CurrentAleo::num_constraints());
        // assert_eq!(178189, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_self_caller() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program caller.aleo;

  record data:
    owner as address.private;
    gates as u64.private;

  function initialize:
    input r0 as data.record;
    cast self.caller r0.gates into r1 as data.record;
    output r1 as data.record;",
        )
        .unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("initialize").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let input =
            Value::from_str(&format!("{{ owner: {caller}.private, gates: 1234u64.private, _nonce: 0group.public }}"))
                .unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [input].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(1)]).unwrap();
        let nonce = CurrentNetwork::g_scalar_multiply(&randomizer);

        // Declare the output value.
        let output =
            Value::from_str(&format!("{{ owner: {caller}.private, gates: 1234u64.private, _nonce: {nonce}.public }}"))
                .unwrap();

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(output, candidate[0]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(output, candidate[0]);

        process.verify_execution::<false>(&execution).unwrap();
    }

    #[test]
    fn test_process_program_id() {
        // Initialize a new program.
        let program = Program::<CurrentNetwork>::from_str(
            r"program id.aleo;

  struct data:
    owner as address;

  function initialize:
    cast id.aleo into r0 as data;
    output r0 as data.private;",
        )
        .unwrap();

        // Declare the program ID.
        let program_id = ProgramID::from_str("id.aleo").unwrap();
        assert_eq!(*program.id(), program_id);

        // Declare the function name.
        let function_name = Identifier::from_str("initialize").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();

        // Authorize the function call.
        let inputs: &[Value<CurrentNetwork>] = &[];
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, inputs.iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Declare the output value.
        let output = Value::from_str(&format!("{{ owner: {} }}", program_id.to_address().unwrap())).unwrap();

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(output, candidate[0]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(1, candidate.len());
        assert_eq!(output, candidate[0]);

        process.verify_execution::<true>(&execution).unwrap();
    }

    #[test]
    fn test_process_execute_call_closure() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    token_amount as u64.private;

// (a + (a + b)) + (a + b) == (3a + 2b)
closure execute:
    input r0 as field;
    input r1 as field;
    add r0 r1 into r2;
    add r0 r2 into r3;
    add r2 r3 into r4;
    output r4 as field;
    output r3 as field;
    output r2 as field;

closure check_not_equal:
    input r0 as field;
    input r1 as field;
    assert.neq r0 r1;

function compute:
    input r0 as field.private;
    input r1 as field.public;
    input r2 as token.record;
    cast r2.owner r2.gates r2.token_amount into r3 as token.record;
    call check_not_equal r0 r1;
    call execute r0 r1 into r4 r5 r6;
    output r3 as token.record;
    output r4 as field.private;
    output r5 as field.private;
    output r6 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

        // Reset the process.
        let process = super::test_helpers::sample_process(&program);

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Prepare a record belonging to the address.
        let record_string = format!(
            "{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: 0group.public }}"
        );

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str("3field").unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("5field").unwrap();
        let r2 = Value::<CurrentNetwork>::from_str(&record_string).unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [r0, r1, r2].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);
        let request = authorization.peek_next().unwrap();

        // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
        let randomizer = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(3)]).unwrap();
        let nonce = CurrentNetwork::g_scalar_multiply(&randomizer);

        // Declare the expected output value.
        let r3 = Value::<CurrentNetwork>::from_str(&format!(
            "{{ owner: {caller}.private, gates: 5u64.private, token_amount: 100u64.private, _nonce: {nonce}.public }}"
        ))
        .unwrap();
        let r4 = Value::from_str("19field").unwrap();
        let r5 = Value::from_str("11field").unwrap();
        let r6 = Value::from_str("8field").unwrap();

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r3, candidate[0]);
        assert_eq!(r4, candidate[1]);
        assert_eq!(r5, candidate[2]);
        assert_eq!(r6, candidate[3]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(4, candidate.len());
        assert_eq!(r3, candidate[0]);
        assert_eq!(r4, candidate[1]);
        assert_eq!(r5, candidate[2]);
        assert_eq!(r6, candidate[3]);

        process.verify_execution::<false>(&execution).unwrap();

        // use circuit::Environment;
        //
        // assert_eq!(37080, CurrentAleo::num_constants());
        // assert_eq!(12, CurrentAleo::num_public());
        // assert_eq!(41630, CurrentAleo::num_private());
        // assert_eq!(41685, CurrentAleo::num_constraints());
        // assert_eq!(159387, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_execute_call_external_function() {
        // Initialize a new program.
        let (string, program0) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

record token:
    owner as address.private;
    gates as u64.private;
    amount as u64.private;

function mint:
    input r0 as address.private;
    input r1 as u64.private;
    cast r0 0u64 r1 into r2 as token.record;
    output r2 as token.record;

function produce_magic_number:
    add 1234u64 0u64 into r0;
    output r0 as u64.private;

function check_magic_number:
    input r0 as u64.private;
    assert.eq r0 1234u64;

function noop:

function transfer:
    input r0 as token.record;
    input r1 as address.private;
    input r2 as u64.private;
    sub r0.amount r2 into r3;
    cast r1 0u64 r2 into r4 as token.record;
    cast r0.owner r0.gates r3 into r5 as token.record;
    output r4 as token.record;
    output r5 as token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Construct the process.
        let mut process = super::test_helpers::sample_process(&program0);
        // Initialize another program.
        let (string, program1) = Program::<CurrentNetwork>::parse(
            r"
import token.aleo;

program wallet.aleo;

function transfer:
    input r0 as token.aleo/token.record;
    input r1 as address.private;
    input r2 as u64.private;
    call token.aleo/noop;
    call token.aleo/produce_magic_number into r3;
    call token.aleo/check_magic_number r3;
    call token.aleo/transfer r0 r1 r2 into r4 r5;
    output r4 as token.aleo/token.record;
    output r5 as token.aleo/token.record;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Add the program to the process.
        process.add_program(&program1).unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Initialize caller 0.
        let caller0_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller0 = Address::try_from(&caller0_private_key).unwrap();

        // Initialize caller 1.
        let caller1_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller1 = Address::try_from(&caller1_private_key).unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("transfer").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&format!(
            "{{ owner: {caller0}.private, gates: 0u64.private, amount: 100u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        let r1 = Value::<CurrentNetwork>::from_str(&caller1.to_string()).unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("99u64").unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller0_private_key, program1.id(), function_name, [r0, r1, r2].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 5);
        println!("\nAuthorize\n{:#?}\n\n", authorization.to_vec_deque());

        let (output_a, output_b) = {
            // Fetch the first request.
            let request = authorization.to_vec_deque().pop_back().unwrap();

            // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
            let randomizer_a = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(4)]).unwrap();
            let nonce_a = CurrentNetwork::g_scalar_multiply(&randomizer_a);

            // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
            let randomizer_b = CurrentNetwork::hash_to_scalar_psd2(&[*request.tvk(), Field::from_u64(5)]).unwrap();
            let nonce_b = CurrentNetwork::g_scalar_multiply(&randomizer_b);

            // Declare the expected output value.
            let output_a = Value::from_str(&format!(
                "{{ owner: {caller1}.private, gates: 0u64.private, amount: 99u64.private, _nonce: {nonce_a}.public }}"
            ))
            .unwrap();
            let output_b = Value::from_str(&format!(
                "{{ owner: {caller0}.private, gates: 0u64.private, amount: 1u64.private, _nonce: {nonce_b}.public }}"
            ))
            .unwrap();

            (output_a, output_b)
        };

        // Check again to make sure we didn't modify the authorization before calling `evaluate`.
        assert_eq!(authorization.len(), 5);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(output_a, candidate[0]);
        assert_eq!(output_b, candidate[1]);

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 5);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(2, candidate.len());
        assert_eq!(output_a, candidate[0]);
        assert_eq!(output_b, candidate[1]);

        process.verify_execution::<false>(&execution).unwrap();

        // use circuit::Environment;
        //
        // assert_eq!(6427, CurrentAleo::num_constants());
        // assert_eq!(8, CurrentAleo::num_public());
        // assert_eq!(21264, CurrentAleo::num_private());
        // assert_eq!(21279, CurrentAleo::num_constraints());
        // assert_eq!(81872, CurrentAleo::num_gates());
        //
        // assert_eq!(18504, CurrentAleo::num_constants());
        // assert_eq!(17, CurrentAleo::num_public());
        // assert_eq!(58791, CurrentAleo::num_private());
        // assert_eq!(58855, CurrentAleo::num_constraints());
        // assert_eq!(215810, CurrentAleo::num_gates());
    }

    #[test]
    fn test_process_execute_and_finalize_increment() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program testing.aleo;

mapping account:
    key owner as address.public;
    value amount as u64.public;

function compute:
    input r0 as address.public;
    input r1 as u64.public;
    input r2 as u64.public;
    add r1 r2 into r3;
    finalize r0 r3;

finalize compute:
    input r0 as address.public;
    input r1 as u64.public;
    increment account[r0] by r1;
",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the program ID.
        let program_id = program.id();
        // Declare the mapping.
        let mapping_name = Identifier::from_str("account").unwrap();
        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

        // Reset the process.
        let mut process = Process::load().unwrap();

        // Initialize a new program store.
        let store = ProgramStore::<_, ProgramMemory<_>>::open(None).unwrap();

        // Add the program to the process.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();
        // Check that the deployment verifies.
        process.verify_deployment::<CurrentAleo, _>(&deployment, rng).unwrap();
        // Finalize the deployment.
        process.finalize_deployment(&store, &deployment).unwrap();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&caller.to_string()).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("3u64").unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("5u64").unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [r0, r1, r2].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Verify the execution.
        process.verify_execution::<true>(&execution).unwrap();

        // Now, finalize the execution.
        process.finalize_execution(&store, &execution).unwrap();

        // Check that the account balance is now 8.
        let candidate =
            store.get_value(program_id, &mapping_name, &Plaintext::from(Literal::Address(caller))).unwrap().unwrap();
        assert_eq!(candidate, Value::from_str("8u64").unwrap());
    }

    #[test]
    fn test_process_execute_and_finalize_increment_decrement() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program testing.aleo;

mapping account:
    key owner as address.public;
    value amount as u64.public;

function compute:
    input r0 as address.public;
    input r1 as u64.public;
    input r2 as u64.public;
    add r1 r2 into r3;
    finalize r0 r3;

finalize compute:
    input r0 as address.public;
    input r1 as u64.public;
    increment account[r0] by r1;
    decrement account[r0] by r1;
",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the program ID.
        let program_id = program.id();
        // Declare the mapping.
        let mapping_name = Identifier::from_str("account").unwrap();
        // Declare the function name.
        let function_name = Identifier::from_str("compute").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

        // Reset the process.
        let mut process = Process::load().unwrap();

        // Initialize a new program store.
        let store = ProgramStore::<_, ProgramMemory<_>>::open(None).unwrap();

        // Add the program to the process.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();
        // Check that the deployment verifies.
        process.verify_deployment::<CurrentAleo, _>(&deployment, rng).unwrap();
        // Finalize the deployment.
        process.finalize_deployment(&store, &deployment).unwrap();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&caller.to_string()).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("3u64").unwrap();
        let r2 = Value::<CurrentNetwork>::from_str("5u64").unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [r0, r1, r2].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Verify the execution.
        process.verify_execution::<true>(&execution).unwrap();

        // Now, finalize the execution.
        process.finalize_execution(&store, &execution).unwrap();

        // Check that the account balance is now 0.
        let candidate =
            store.get_value(program_id, &mapping_name, &Plaintext::from(Literal::Address(caller))).unwrap().unwrap();
        assert_eq!(candidate, Value::from_str("0u64").unwrap());
    }

    #[test]
    fn test_process_execute_mint_public() {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

// On-chain storage of an `account` map, with `owner` as the key,
// and `amount` as the value.
mapping account:
    // The token owner.
    key owner as address.public;
    // The token amount.
    value amount as u64.public;

// The function `mint_public` issues the specified token amount
// for the token receiver publicly on the network.
function mint_public:
    // Input the token receiver.
    input r0 as address.public;
    // Input the token amount.
    input r1 as u64.public;
    // Mint the tokens publicly.
    finalize r0 r1;

// The finalize scope of `mint_public` increments the
// `account` of the token receiver by the specified amount.
finalize mint_public:
    // Input the token receiver.
    input r0 as address.public;
    // Input the token amount.
    input r1 as u64.public;

    // Increments `account[r0]` by `r1`.
    // If `account[r0]` does not exist, it will be created.
    // If `account[r0] + r1` overflows, `mint_public` is reverted.
    increment account[r0] by r1;
",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the program ID.
        let program_id = program.id();
        // Declare the mapping.
        let mapping_name = Identifier::from_str("account").unwrap();
        // Declare the function name.
        let function_name = Identifier::from_str("mint_public").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

        // Reset the process.
        let mut process = Process::load().unwrap();

        // Initialize a new program store.
        let store = ProgramStore::<_, ProgramMemory<_>>::open(None).unwrap();

        // Add the program to the process.
        let deployment = process.deploy::<CurrentAleo, _>(&program, rng).unwrap();
        // Check that the deployment verifies.
        process.verify_deployment::<CurrentAleo, _>(&deployment, rng).unwrap();
        // Finalize the deployment.
        process.finalize_deployment(&store, &deployment).unwrap();

        // TODO (howardwu): Remove this. I call this to synthesize the proving key independent of the assignment from 'execute'.
        //  In general, we should update all tests to utilize a presynthesized proving key, before execution, to test
        //  the correctness of the synthesizer.
        process.synthesize_key::<CurrentAleo, _>(program.id(), &function_name, rng).unwrap();

        // Initialize a new caller account.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let _caller_view_key = ViewKey::try_from(&caller_private_key).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&caller.to_string()).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("3u64").unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program.id(), function_name, [r0, r1].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 1);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 1);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Verify the execution.
        process.verify_execution::<true>(&execution).unwrap();

        // Now, finalize the execution.
        process.finalize_execution(&store, &execution).unwrap();

        // Check the account balance.
        let candidate =
            store.get_value(program_id, &mapping_name, &Plaintext::from(Literal::Address(caller))).unwrap().unwrap();
        assert_eq!(candidate, Value::from_str("3u64").unwrap());
    }

    #[test]
    fn test_process_execute_call_mint_public() {
        // Initialize a new program.
        let (string, program0) = Program::<CurrentNetwork>::parse(
            r"
program token.aleo;

// On-chain storage of an `account` map, with `owner` as the key,
// and `amount` as the value.
mapping account:
    // The token owner.
    key owner as address.public;
    // The token amount.
    value amount as u64.public;

// The function `mint_public` issues the specified token amount
// for the token receiver publicly on the network.
function mint_public:
    // Input the token receiver.
    input r0 as address.public;
    // Input the token amount.
    input r1 as u64.public;
    // Mint the tokens publicly.
    finalize r0 r1;

// The finalize scope of `mint_public` increments the
// `account` of the token receiver by the specified amount.
finalize mint_public:
    // Input the token receiver.
    input r0 as address.public;
    // Input the token amount.
    input r1 as u64.public;

    // Increments `account[r0]` by `r1`.
    // If `account[r0]` does not exist, it will be created.
    // If `account[r0] + r1` overflows, `mint_public` is reverted.
    increment account[r0] by r1;
",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Declare the mapping.
        let mapping_name = Identifier::from_str("account").unwrap();
        // Declare the function name.
        let function_name = Identifier::from_str("mint_public").unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Construct the process.
        let process = super::test_helpers::sample_process(&program0);
        // Check that the circuit key can be synthesized.
        process.synthesize_key::<CurrentAleo, _>(program0.id(), &function_name, rng).unwrap();

        // Reset the process.
        let mut process = Process::load().unwrap();

        // Initialize a new program store.
        let store = ProgramStore::<_, ProgramMemory<_>>::open(None).unwrap();

        // Add the program to the process.
        let deployment = process.deploy::<CurrentAleo, _>(&program0, rng).unwrap();
        // Check that the deployment verifies.
        process.verify_deployment::<CurrentAleo, _>(&deployment, rng).unwrap();
        // Finalize the deployment.
        process.finalize_deployment(&store, &deployment).unwrap();

        // TODO (howardwu): Remove this. I call this to synthesize the proving key independent of the assignment from 'execute'.
        //  In general, we should update all tests to utilize a presynthesized proving key, before execution, to test
        //  the correctness of the synthesizer.
        process.synthesize_key::<CurrentAleo, _>(program0.id(), &function_name, rng).unwrap();

        // Initialize another program.
        let (string, program1) = Program::<CurrentNetwork>::parse(
            r"
import token.aleo;

program public_wallet.aleo;

function mint:
    input r0 as address.public;
    input r1 as u64.public;
    call token.aleo/mint_public r0 r1;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Add the program to the process.
        process.add_program(&program1).unwrap();

        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Initialize caller.
        let caller_private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let caller = Address::try_from(&caller_private_key).unwrap();

        // Declare the function name.
        let function_name = Identifier::from_str("mint").unwrap();

        // Declare the input value.
        let r0 = Value::<CurrentNetwork>::from_str(&caller.to_string()).unwrap();
        let r1 = Value::<CurrentNetwork>::from_str("100u64").unwrap();

        // Authorize the function call.
        let authorization = process
            .authorize::<CurrentAleo, _>(&caller_private_key, program1.id(), function_name, [r0, r1].iter(), rng)
            .unwrap();
        assert_eq!(authorization.len(), 2);

        // Compute the output value.
        let response = process.evaluate::<CurrentAleo>(authorization.replicate()).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Check again to make sure we didn't modify the authorization after calling `evaluate`.
        assert_eq!(authorization.len(), 2);

        // Execute the request.
        let (response, execution, _inclusion, _metrics) =
            process.execute::<CurrentAleo, _>(authorization, rng).unwrap();
        let candidate = response.outputs();
        assert_eq!(0, candidate.len());

        // Verify the execution.
        process.verify_execution::<true>(&execution).unwrap();

        // Now, finalize the execution.
        process.finalize_execution(&store, &execution).unwrap();

        // Check the account balance.
        let candidate =
            store.get_value(program0.id(), &mapping_name, &Plaintext::from(Literal::Address(caller))).unwrap().unwrap();
        assert_eq!(candidate, Value::from_str("100u64").unwrap());
    }
}
