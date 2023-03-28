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

impl<N: Network> FromBytes for Table<N> {
    /// Reads the table from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the table name.
        let name = Identifier::<N>::read_le(&mut reader)?;

        // Read the inputs.
        let num_inputs = u16::read_le(&mut reader)?;
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(TableInput::read_le(&mut reader)?);
        }

        // Read the outputs.
        let num_outputs = u16::read_le(&mut reader)?;
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(TableOutput::read_le(&mut reader)?);
        }

        // Return the new mapping.
        Ok(Self::new(name, inputs, outputs))
    }
}

impl<N: Network> ToBytes for Table<N> {
    /// Writes the table to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the table name.
        self.name.write_le(&mut writer)?;
        // Write the number of inputs.
        (self.inputs.len() as u16).write_le(&mut writer)?;
        // Write the inputs.
        for input in self.inputs.iter() {
            input.write_le(&mut writer)?;
        }
        // Write the number of outputs.
        (self.outputs.len() as u16).write_le(&mut writer)?;
        // Write the outputs.
        for output in self.outputs.iter() {
            output.write_le(&mut writer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_mapping_bytes() -> Result<()> {
        let mapping_string = r"
table adder:
    input field;
    output field;";

        let expected = Table::<CurrentNetwork>::from_str(mapping_string)?;
        let expected_bytes = expected.to_bytes_le()?;
        println!("String size: {:?}, Bytecode size: {:?}", mapping_string.as_bytes().len(), expected_bytes.len());

        let candidate = Table::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected.to_string(), candidate.to_string());
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
