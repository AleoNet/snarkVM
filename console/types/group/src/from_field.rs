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

impl<E: Environment> FromField for Group<E> {
    type Field = Field<E>;

    /// Initializes a new group by recovering the **x-coordinate** of an affine group from a field element.
    fn from_field(field: &Self::Field) -> Result<Self> {
        Group::from_x_coordinate(*field)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_from_field() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let expected = Group::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));
            let candidate = Group::<CurrentEnvironment>::from_field(&expected.to_field()?)?;
            assert_eq!(expected, candidate);
        }
        Ok(())
    }

    #[test]
    fn test_from_field() -> Result<()> {
        check_from_field()
    }
}
