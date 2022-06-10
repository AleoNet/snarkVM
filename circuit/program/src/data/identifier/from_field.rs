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

impl<A: Aleo> FromField for Identifier<A> {
    type Field = Field<A>;

    /// Initializes a new identifier from a field element.
    fn from_field(field: Self::Field) -> Self {
        // Convert the field to a list of little-endian bits.
        Self::from_bits_le(&field.to_bits_le())
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{data::identifier::tests::sample_console_identifier, Circuit};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    fn check_from_field(num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) -> Result<()> {
        for _ in 0..ITERATIONS {
            // Initialize the console identifier.
            let console_identifier = sample_console_identifier::<Circuit>()?;
            // Initialize the circuit list of bits.
            let circuit_field = Field::constant(console::ToField::to_field(&console_identifier)?);

            Circuit::scope("Identifier FromField", || {
                let candidate = Identifier::<Circuit>::from_field(circuit_field);
                assert_eq!(Mode::Constant, candidate.eject_mode());
                assert_eq!(console_identifier, candidate.eject_value());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_from_field() -> Result<()> {
        check_from_field(253, 0, 0, 0)
    }
}
