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

impl<N: Network> FromBytes for Finalize<N> {
    /// Reads the finalize from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the associated function name.
        let name = Identifier::<N>::read_le(&mut reader)?;

        // Read the inputs.
        let num_inputs = u16::read_le(&mut reader)?;
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(Input::read_le(&mut reader)?);
        }

        // Read the commands.
        let num_commands = u16::read_le(&mut reader)?;
        if num_commands > N::MAX_COMMANDS as u16 {
            return Err(error(format!("Failed to deserialize finalize: too many commands ({num_commands})")));
        }
        let mut commands = Vec::with_capacity(num_commands as usize);
        for _ in 0..num_commands {
            commands.push(Command::read_le(&mut reader)?);
        }

        // Read the outputs.
        let num_outputs = u16::read_le(&mut reader)?;
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(Output::read_le(&mut reader)?);
        }

        // Initialize a new finalize.
        let mut finalize = Self::new(name);
        inputs.into_iter().try_for_each(|input| finalize.add_input(input)).map_err(|e| error(e.to_string()))?;
        commands.into_iter().try_for_each(|command| finalize.add_command(command)).map_err(|e| error(e.to_string()))?;
        outputs.into_iter().try_for_each(|output| finalize.add_output(output)).map_err(|e| error(e.to_string()))?;

        Ok(finalize)
    }
}

impl<N: Network> ToBytes for Finalize<N> {
    /// Writes the finalize to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the associated function name.
        self.name.write_le(&mut writer)?;

        // Write the number of inputs for the finalize.
        let num_inputs = self.inputs.len();
        match num_inputs <= N::MAX_INPUTS {
            true => (num_inputs as u16).write_le(&mut writer)?,
            false => return Err(error(format!("Failed to write {num_inputs} inputs as bytes"))),
        }

        // Write the inputs.
        for input in self.inputs.iter() {
            input.write_le(&mut writer)?;
        }

        // Write the number of commands for the finalize.
        let num_commands = self.commands.len();
        match num_commands <= N::MAX_COMMANDS {
            true => (num_commands as u16).write_le(&mut writer)?,
            false => return Err(error(format!("Failed to write {num_commands} commands as bytes"))),
        }

        // Write the commands.
        for command in self.commands.iter() {
            command.write_le(&mut writer)?;
        }

        // Write the number of outputs for the finalize.
        let num_outputs = self.outputs.len();
        match num_outputs <= N::MAX_OUTPUTS {
            true => (num_outputs as u16).write_le(&mut writer)?,
            false => return Err(error(format!("Failed to write {num_outputs} outputs as bytes"))),
        }

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
    fn test_finalize_bytes() -> Result<()> {
        let finalize_string = r"
finalize main:
    input r0 as field.public;
    input r1 as field.public;
    add r0 r1 into r2;
    add r0 r1 into r3;
    add r0 r1 into r4;
    add r0 r1 into r5;
    add r0 r1 into r6;
    add r0 r1 into r7;
    add r0 r1 into r8;
    add r0 r1 into r9;
    add r0 r1 into r10;
    add r0 r1 into r11;
    output r11 as field.public;";

        let expected = Finalize::<CurrentNetwork>::from_str(finalize_string)?;
        let expected_bytes = expected.to_bytes_le()?;
        println!("String size: {:?}, Bytecode size: {:?}", finalize_string.as_bytes().len(), expected_bytes.len());

        let candidate = Finalize::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected.to_string(), candidate.to_string());
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
