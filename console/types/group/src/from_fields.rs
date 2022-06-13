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

impl<E: Environment> FromFields for Group<E> {
    type Field = Field<E>;

    /// Initializes a new group by recovering the **x-coordinate** of an affine group from a field element.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        // Ensure there is exactly one field element in the vector.
        ensure!(fields.len() == 1, "Group must be recovered from a single field element");
        // Recover the group from the field element.
        Self::from_field(&fields[0])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    fn check_from_fields() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let expected = Group::<CurrentEnvironment>::new(Uniform::rand(&mut test_rng()));
            let candidate = Group::<CurrentEnvironment>::from_fields(&expected.to_fields()?)?;
            assert_eq!(expected, candidate);
        }
        Ok(())
    }

    #[test]
    fn test_from_fields() -> Result<()> {
        check_from_fields()
    }
}
