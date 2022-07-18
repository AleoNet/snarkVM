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

mod bytes;
mod serialize;
mod string;

use crate::{Certificate, Program, VerifyingKey};
use console::{network::prelude::*, program::Identifier};

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub struct Deployment<N: Network> {
    /// The edition.
    edition: u16,
    /// The program.
    program: Program<N>,
    /// The mapping of function names to their verifying key and certificate.
    verifying_keys: IndexMap<Identifier<N>, (VerifyingKey<N>, Certificate<N>)>,
}

impl<N: Network> Deployment<N> {
    /// Initializes a new deployment.
    pub fn new(
        edition: u16,
        program: Program<N>,
        verifying_keys: IndexMap<Identifier<N>, (VerifyingKey<N>, Certificate<N>)>,
    ) -> Self {
        Self { edition, program, verifying_keys }
    }

    /// Returns the edition.
    pub const fn edition(&self) -> u16 {
        self.edition
    }

    /// Returns the program.
    pub const fn program(&self) -> &Program<N> {
        &self.program
    }

    /// Returns the verifying keys.
    pub const fn verifying_keys(&self) -> &IndexMap<Identifier<N>, (VerifyingKey<N>, Certificate<N>)> {
        &self.verifying_keys
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use crate::{Process, Program};
    use console::network::Testnet3;

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
    input r1 as u32.public;
    add r0 r1 into r2;
    output r2 as u32.public;",
                )
                .unwrap();
                assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

                // Initialize the RNG.
                let rng = &mut test_crypto_rng();

                // Construct the process.
                let process = Process::<CurrentNetwork>::new().unwrap();
                // Compute the stack.
                let stack = process.compute_stack(&program).unwrap();
                // Compute the deployment.
                stack.deploy::<CurrentAleo, _>(rng).unwrap()
            })
            .clone()
    }
}
