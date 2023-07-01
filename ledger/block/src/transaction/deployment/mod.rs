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

mod bytes;
mod serialize;
mod string;

use crate::Transaction;
use console::{
    network::prelude::*,
    program::{Identifier, ProgramID},
    types::Field,
};
use synthesizer_program::Program;
use synthesizer_snark::{Certificate, VerifyingKey};

#[derive(Clone, PartialEq, Eq)]
pub struct Deployment<N: Network> {
    /// The edition.
    edition: u16,
    /// The program.
    program: Program<N>,
    /// The mapping of function names to their verifying key and certificate.
    verifying_keys: Vec<(Identifier<N>, (VerifyingKey<N>, Certificate<N>))>,
}

impl<N: Network> Deployment<N> {
    /// Initializes a new deployment.
    pub fn new(
        edition: u16,
        program: Program<N>,
        verifying_keys: Vec<(Identifier<N>, (VerifyingKey<N>, Certificate<N>))>,
    ) -> Result<Self> {
        // Construct the deployment.
        let deployment = Self { edition, program, verifying_keys };
        // Ensure the deployment is ordered.
        deployment.check_is_ordered()?;
        // Return the deployment.
        Ok(deployment)
    }

    /// Checks that the deployment is ordered.
    pub fn check_is_ordered(&self) -> Result<()> {
        let program_id = self.program.id();

        // Ensure the edition matches.
        ensure!(
            self.edition == N::EDITION,
            "Deployed the wrong edition (expected '{}', found '{}').",
            N::EDITION,
            self.edition
        );
        // Ensure the program contains functions.
        ensure!(
            !self.program.functions().is_empty(),
            "No functions present in the deployment for program '{program_id}'"
        );
        // Ensure the deployment contains verifying keys.
        ensure!(
            !self.verifying_keys.is_empty(),
            "No verifying keys present in the deployment for program '{program_id}'"
        );

        // Ensure the number of functions matches the number of verifying keys.
        if self.program.functions().len() != self.verifying_keys.len() {
            bail!("Deployment has an incorrect number of verifying keys, according to the program.");
        }

        // Ensure the function and verifying keys correspond.
        for ((function_name, function), (name, _)) in self.program.functions().iter().zip_eq(&self.verifying_keys) {
            // Ensure the function name is correct.
            if function_name != function.name() {
                bail!("The function key is '{function_name}', but the function name is '{}'", function.name())
            }
            // Ensure the function name with the verifying key is correct.
            if name != function.name() {
                bail!("The verifier key is '{name}', but the function name is '{}'", function.name())
            }
        }

        ensure!(
            !has_duplicates(self.verifying_keys.iter().map(|(name, ..)| name)),
            "A duplicate function name was found"
        );

        Ok(())
    }

    /// Returns the size in bytes.
    pub fn size_in_bytes(&self) -> Result<u64> {
        Ok(u64::try_from(self.to_bytes_le()?.len())?)
    }

    /// Returns the edition.
    pub const fn edition(&self) -> u16 {
        self.edition
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the program.
    pub const fn program_id(&self) -> &ProgramID<N> {
        self.program.id()
    }

    /// Returns the verifying keys.
    pub const fn verifying_keys(&self) -> &Vec<(Identifier<N>, (VerifyingKey<N>, Certificate<N>))> {
        &self.verifying_keys
    }

    /// Returns the deployment ID.
    pub fn to_deployment_id(&self) -> Result<Field<N>> {
        Ok(*Transaction::deployment_tree(self, None)?.root())
    }
}

#[cfg(any(test, feature = "test"))]
pub mod test_helpers {
    use super::*;
    use console::network::Testnet3;
    use synthesizer_process::Process;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = circuit::network::AleoV0;

    pub(crate) fn sample_deployment() -> Deployment<CurrentNetwork> {
        static INSTANCE: OnceCell<Deployment<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Initialize a new program.
                let (string, program) = Program::<CurrentNetwork>::parse(
                    r"
program testing.aleo;

function compute:
    input r0 as u32.private;
    add r0 r0 into r1;
    output r1 as u32.public;",
                )
                .unwrap();
                assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

                // Initialize the RNG.
                let rng = &mut TestRng::default();

                // Construct the process.
                let process = Process::load().unwrap();
                // Compute the deployment.
                // Note: This is a hack to work around Rust's dependency cycle rules.
                let deployment_string = process.deploy::<CurrentAleo, _>(&program, rng).unwrap().to_string();
                // Return the deployment.
                Deployment::from_str(&deployment_string).unwrap()
            })
            .clone()
    }
}
