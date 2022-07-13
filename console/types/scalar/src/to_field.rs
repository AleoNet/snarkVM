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

impl<E: Environment> ToField for Scalar<E> {
    type Field = Field<E>;

    /// Returns the scalar as a field element.
    fn to_field(&self) -> Result<Self::Field> {
        // Note: We are reconstituting the scalar field into a base field.
        // This is safe as the scalar field modulus is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(Scalar::<E>::size_in_bits() < Field::<E>::size_in_bits());

        Field::<E>::from_bits_le(&self.to_bits_le())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_to_field() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a random value.
            let scalar: Scalar<CurrentEnvironment> = Uniform::rand(&mut test_rng());

            let candidate = scalar.to_field()?;

            let expected = scalar.to_bits_le();
            for (index, candidate_bit) in candidate.to_bits_le().iter().enumerate() {
                match index < Scalar::<CurrentEnvironment>::size_in_bits() {
                    true => assert_eq!(expected[index], *candidate_bit),
                    false => assert!(!*candidate_bit),
                }
            }
        }
        Ok(())
    }
}
