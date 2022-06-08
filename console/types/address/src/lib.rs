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
mod parse;
mod serialize;

pub use snarkvm_console_network::prelude::*;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_group::Group;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Address<N: Network> {
    /// The underlying address.
    address: Group<N>,
}

impl<N: Network> AddressTrait for Address<N> {}

impl<N: Network> Address<N> {
    /// Initializes an address from a group element.
    pub const fn new(group: Group<N>) -> Self {
        Self { address: group }
    }
}

impl<N: Network> TypeName for Address<N> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "address"
    }
}

impl<N: Network> Deref for Address<N> {
    type Target = Group<N>;

    /// Returns the address as a group element.
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.address
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::test_crypto_rng;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_deref() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = Address::try_from(private_key)?;

            // Check the group representation.
            let candidate = *expected;
            assert_eq!(expected, Address::new(candidate));
        }
        Ok(())
    }
}
