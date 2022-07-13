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

impl<N: Network> FromBytes for Closure<N> {
    /// Reads the closure from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the closure name.
        let name = Identifier::<N>::read_le(&mut reader)?;

        // Read the inputs.
        let num_inputs = u16::read_le(&mut reader)?;
        let mut inputs = Vec::with_capacity(num_inputs as usize);
        for _ in 0..num_inputs {
            inputs.push(Input::read_le(&mut reader)?);
        }

        // Read the instructions.
        let num_instructions = u32::read_le(&mut reader)?;
        let mut instructions = Vec::with_capacity(num_instructions as usize);
        for _ in 0..num_instructions {
            instructions.push(Instruction::read_le(&mut reader)?);
        }

        // Read the outputs.
        let num_outputs = u16::read_le(&mut reader)?;
        let mut outputs = Vec::with_capacity(num_outputs as usize);
        for _ in 0..num_outputs {
            outputs.push(Output::read_le(&mut reader)?);
        }

        // Initialize a new closure.
        let mut closure = Self::new(name);
        inputs.into_iter().try_for_each(|input| closure.add_input(input)).map_err(|e| error(e.to_string()))?;
        instructions
            .into_iter()
            .try_for_each(|instruction| closure.add_instruction(instruction))
            .map_err(|e| error(e.to_string()))?;
        outputs.into_iter().try_for_each(|output| closure.add_output(output)).map_err(|e| error(e.to_string()))?;

        Ok(closure)
    }
}

impl<N: Network> ToBytes for Closure<N> {
    /// Writes the closure to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the closure name.
        self.name.write_le(&mut writer)?;

        // Write the number of inputs for the closure.
        let num_inputs = self.inputs.len();
        match num_inputs <= N::MAX_INPUTS {
            true => (num_inputs as u16).write_le(&mut writer)?,
            false => return Err(error(format!("Failed to write {num_inputs} inputs as bytes"))),
        }

        // Write the inputs.
        for input in self.inputs.iter() {
            input.write_le(&mut writer)?;
        }

        // Write the number of instructions for the closure.
        let num_instructions = self.instructions.len();
        match num_instructions <= N::MAX_FUNCTION_INSTRUCTIONS {
            true => (num_instructions as u32).write_le(&mut writer)?,
            false => return Err(error(format!("Failed to write {num_instructions} instructions as bytes"))),
        }

        // Write the instructions.
        for instruction in self.instructions.iter() {
            instruction.write_le(&mut writer)?;
        }

        // Write the number of outputs for the closure.
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
    fn test_closure_bytes() -> Result<()> {
        let closure_string = r"
closure main:
    input r0 as field;
    input r1 as field;
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
    output r11 as field;";

        let expected = Closure::<CurrentNetwork>::from_str(closure_string)?;
        let expected_bytes = expected.to_bytes_le()?;
        println!("String size: {:?}, Bytecode size: {:?}", closure_string.as_bytes().len(), expected_bytes.len());

        let candidate = Closure::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected.to_string(), candidate.to_string());
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
