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

impl<A: Aleo> PrivateKey<A> {
    /// Returns the account compute key for this account private key.
    pub fn to_compute_key(&self) -> ComputeKey<A> {
        ComputeKey::from_private_key(self)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{helpers::generate_account, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_to_compute_key(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for i in 0..ITERATIONS {
            // Generate a private key, compute key, view key, and address.
            let (private_key, compute_key, _view_key, _address) = generate_account()?;

            // Initialize the private key.
            let candidate = PrivateKey::<Circuit>::new(mode, private_key);

            Circuit::scope(&format!("{} {}", mode, i), || {
                let candidate = candidate.to_compute_key();
                assert_eq!(compute_key, candidate.eject_value());
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
    fn test_to_compute_key_constant() -> Result<()> {
        check_to_compute_key(Mode::Constant, 2758, 0, 0, 0)
    }

    #[test]
    fn test_to_compute_key_public() -> Result<()> {
        check_to_compute_key(Mode::Public, 1001, 0, 3595, 3598)
    }

    #[test]
    fn test_to_compute_key_private() -> Result<()> {
        check_to_compute_key(Mode::Private, 1001, 0, 3595, 3598)
    }
}
