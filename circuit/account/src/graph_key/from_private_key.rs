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

use super::*;

impl<A: Aleo> GraphKey<A> {
    /// Returns the account graph key for this account private key.
    pub fn from_private_key(private_key: &PrivateKey<A>) -> Self {
        // Compute sk_tag := T^sk_sig.
        let sk_tag = A::t_scalar_multiply(private_key.sk_sig());
        // Output the graph key.
        Self { sk_tag }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{helpers::generate_account, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_from_private_key(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for i in 0..ITERATIONS {
            // Generate a private key and graph key.
            let (private_key, _, _, _) = generate_account()?;
            let graph_key = console::GraphKey::try_from(&private_key)?;

            // Initialize the private key.
            let private_key = PrivateKey::<Circuit>::new(mode, private_key);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = GraphKey::from_private_key(&private_key);
                assert_eq!(graph_key, candidate.eject_value());
                // TODO (howardwu): Resolve skipping the cost count checks for the burn-in round.
                if i > 0 {
                    assert_scope!(<=num_constants, num_public, num_private, num_constraints);
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_from_private_key_constant() -> Result<()> {
        check_from_private_key(Mode::Constant, 1400, 0, 0, 0)
    }

    #[test]
    fn test_from_private_key_public() -> Result<()> {
        check_from_private_key(Mode::Public, 500, 0, 1501, 1502)
    }

    #[test]
    fn test_from_private_key_private() -> Result<()> {
        check_from_private_key(Mode::Private, 500, 0, 1501, 1502)
    }
}
