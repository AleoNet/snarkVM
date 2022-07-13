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
mod try_from;

#[cfg(feature = "compute_key")]
use crate::ComputeKey;
#[cfg(feature = "private_key")]
use crate::PrivateKey;

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::Scalar;

use base58::{FromBase58, ToBase58};

/// The account view key used to decrypt records and ciphertext.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ViewKey<N: Network>(Scalar<N>);

impl<N: Network> ViewKey<N> {
    /// Initializes the account view key from a scalar.
    pub const fn from_scalar(view_key: Scalar<N>) -> Self {
        Self(view_key)
    }
}

impl<N: Network> Deref for ViewKey<N> {
    type Target = Scalar<N>;

    /// Returns the account view key as a scalar.
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_from_scalar() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = ViewKey::try_from(private_key)?;

            // Check the scalar representation.
            let candidate = *expected;
            assert_eq!(expected, ViewKey::from_scalar(candidate));
        }
        Ok(())
    }
}
