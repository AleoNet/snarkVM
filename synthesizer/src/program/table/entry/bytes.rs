// Copyright (C) 2019-2023 Aleo Systems Inc.
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

impl<N: Network> FromBytes for Entry<N> {
    /// Reads the input statement from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of inputs.
        let num_inputs = u16::read_le(&mut reader)?;
        // Read the inputs.
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(Literal::read_le(&mut reader)?);
        }

        // Read the number of outputs.
        let num_outputs = u16::read_le(&mut reader)?;
        // Read the outputs.
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(Literal::read_le(&mut reader)?);
        }

        Ok(Self { inputs, outputs })
    }
}

impl<N: Network> ToBytes for Entry<N> {
    /// Writes the input statement to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the number of inputs.
        (self.inputs.len() as u16).write_le(&mut writer)?;
        // Write the inputs.
        self.inputs.iter().try_for_each(|input| input.write_le(&mut writer))?;

        // Write the number of outputs.
        (self.outputs.len() as u16).write_le(&mut writer)?;
        // Write the outputs.
        self.outputs.iter().try_for_each(|output| output.write_le(&mut writer))?;

        Ok(())
    }
}
