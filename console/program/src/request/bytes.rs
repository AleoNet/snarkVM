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

impl<N: Network> FromBytes for Request<N> {
    /// Reads the request from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let caller = Address::read_le(&mut reader)?;
        let network_id = U16::new(u16::read_le(&mut reader)?);
        let program_id = ProgramID::read_le(&mut reader)?;
        let function_name = Identifier::read_le(&mut reader)?;

        let inputs_len = u16::read_le(&mut reader)? as usize;
        let inputs = (0..inputs_len).map(|_| Value::read_le(&mut reader)).collect::<Result<Vec<_>, _>>()?;

        Ok(Self {
            caller,
            network_id,
            program_id,
            function_name,
            inputs,
        })
    }
}

impl<N: Network> ToBytes for Request<N> {
    /// Writes the request to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.caller.write_le(&mut writer)?;
        self.network_id.write_le(&mut writer)?;
        self.program_id.write_le(&mut writer)?;
        self.function_name.write_le(&mut writer)?;

        if self.inputs.len() > u16::MAX as usize {
            return Err(error(format!("Failed to write request. Too many inputs: '{}'", self.inputs.len())));
        }

        (self.inputs.len() as u16).write_le(&mut writer)?;
        for input in &self.inputs {
            input.write_le(&mut writer)?;
        }

        Ok(())
    }
}
