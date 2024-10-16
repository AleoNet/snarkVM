// Copyright 2024 Aleo Network Foundation
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

use super::*;

impl<A: Aleo> PrivateKey<A> {
    /// Returns the account compute key for this account private key.
    pub fn to_compute_key(&self) -> ComputeKey<A> {
        ComputeKey::from_private_key(self)
    }
}

#[cfg(all(test, feature = "console"))]
mod tests {
    use super::*;
    use crate::{Circuit, helpers::generate_account};

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

            Circuit::scope(format!("{mode} {i}"), || {
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
        check_to_compute_key(Mode::Public, 1001, 0, 4347, 4353)
    }

    #[test]
    fn test_to_compute_key_private() -> Result<()> {
        check_to_compute_key(Mode::Private, 1001, 0, 4347, 4353)
    }
}
