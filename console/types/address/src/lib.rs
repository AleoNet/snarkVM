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

mod bitwise;
mod bytes;
mod from_bits;
mod from_field;
mod from_fields;
mod parse;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod to_field;
mod to_fields;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_group::Group;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Address<E: Environment> {
    /// The underlying address.
    address: Group<E>,
}

impl<E: Environment> AddressTrait for Address<E> {}

impl<E: Environment> Visibility for Address<E> {
    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> Result<u16> {
        Ok(1)
    }
}

impl<E: Environment> Address<E> {
    /// Initializes an address from a group element.
    pub const fn new(group: Group<E>) -> Self {
        Self { address: group }
    }

    /// Initializes a `zero` address.
    #[deprecated(since = "0.1.0", note = "This is used for **testing** purposes")]
    pub fn zero() -> Self {
        Self::new(Group::zero())
    }

    /// Initializes a "random" address.
    #[deprecated(since = "0.1.0", note = "This is used for **testing** purposes")]
    pub fn rand<R: Rng>(rng: &mut R) -> Self {
        Self::new(Group::rand(rng))
    }
}

impl<E: Environment> TypeName for Address<E> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "address"
    }
}

impl<E: Environment> Deref for Address<E> {
    type Target = Group<E>;

    /// Returns the address as a group element.
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.address
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_deref() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let expected = Address::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));

            // Check the group representation.
            let candidate = *expected;
            assert_eq!(expected, Address::new(candidate));
        }
        Ok(())
    }
}
