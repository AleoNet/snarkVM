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

mod from_private_key;
mod to_address;

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

use crate::PrivateKey;
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{environment::prelude::*, Address, Scalar};

use core::ops::Deref;

/// The account view key is able to decrypt records and ciphertext.
pub struct ViewKey<A: Aleo>(Scalar<A>);

#[cfg(console)]
impl<A: Aleo> Inject for ViewKey<A> {
    type Primitive = console::ViewKey<A::Network>;

    /// Initializes an account view key from the given mode and scalar field element.
    fn new(mode: Mode, view_key: Self::Primitive) -> ViewKey<A> {
        Self(Scalar::new(mode, *view_key))
    }
}

#[cfg(console)]
impl<A: Aleo> Eject for ViewKey<A> {
    type Primitive = console::ViewKey<A::Network>;

    /// Ejects the mode of the view key.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the view key as a scalar field element.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from_scalar(self.0.eject_value())
    }
}

impl<A: Aleo> Deref for ViewKey<A> {
    type Target = Scalar<A>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{helpers::generate_account, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 500;

    fn check_new(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Generate a private key, compute key, view key, and address.
            let (_private_key, _compute_key, view_key, _address) = generate_account()?;

            Circuit::scope(format!("New {mode}"), || {
                let candidate = ViewKey::<Circuit>::new(mode, view_key);
                assert_eq!(mode, candidate.eject_mode());
                assert_eq!(view_key, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_view_key_new_constant() -> Result<()> {
        check_new(Mode::Constant, 1, 0, 0, 0)
    }

    #[test]
    fn test_view_key_new_public() -> Result<()> {
        check_new(Mode::Public, 0, 1, 0, 0)
    }

    #[test]
    fn test_view_key_new_private() -> Result<()> {
        check_new(Mode::Private, 0, 0, 1, 0)
    }
}
