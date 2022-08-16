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

impl<A: Aleo> ProgramID<A> {
    /// Returns the program address for this program ID.
    pub fn to_address(&self) -> Address<A> {
        // Compute the program address as `HashToGroup(program_id)`.
        let group = A::hash_to_group_psd4(&[self.name().to_field(), self.network().to_field()]);
        // Return the program address.
        Address::from_group(group)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{data::identifier::tests::sample_console_identifier_as_string, Circuit};

    use anyhow::Result;

    const ITERATIONS: usize = 100;

    fn check_to_address(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        for i in 0..ITERATIONS {
            // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
            let expected_name_string = sample_console_identifier_as_string::<Circuit>()?;
            let expected_program_id = console::ProgramID::<<Circuit as Environment>::Network>::from_str(&format!(
                "{expected_name_string}.aleo"
            ))?;
            let expected = expected_program_id.to_address()?;

            let program_id = ProgramID::<Circuit>::new(mode, expected_program_id);

            Circuit::scope(format!("{mode}"), || {
                let candidate = program_id.to_address();
                assert_eq!(expected, candidate.eject_value());
                if i > 0 {
                    assert_scope!(num_constants, num_public, num_private, num_constraints);
                }
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_to_address_constant() -> Result<()> {
        check_to_address(Mode::Constant, 553, 0, 0, 0)
    }

    #[test]
    fn test_to_address_public() -> Result<()> {
        check_to_address(Mode::Public, 553, 0, 0, 0)
    }

    #[test]
    fn test_to_address_private() -> Result<()> {
        check_to_address(Mode::Private, 553, 0, 0, 0)
    }
}
