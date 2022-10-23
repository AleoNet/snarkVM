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

impl<N: Network> FromBytes for Input<N> {
    /// Reads the input from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let register = FromBytes::read_le(&mut reader)?;
        let register_type = FromBytes::read_le(&mut reader)?;

        // Ensure the register is not a register member.
        match matches!(register, Register::Locator(..)) {
            true => Ok(Self { register, register_type }),
            false => Err(error(format!("Input '{register}' cannot be a register member"))),
        }
    }
}

impl<N: Network> ToBytes for Input<N> {
    /// Writes the input to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the register is not a register member.
        if !matches!(self.register, Register::Locator(..)) {
            return Err(error(format!("Input '{}' cannot be a register member", self.register)));
        }
        self.register.write_le(&mut writer)?;
        self.register_type.write_le(&mut writer)
    }
}
