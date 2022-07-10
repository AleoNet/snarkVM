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

impl<N: Network> FromBytes for Instruction<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        /// Creates a match statement that produces the `FromBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_from_bytes_le!(self, |reader| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_from_bytes_le {
            ($object:expr, |$reader:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // Read the opcode index.
                let index = u16::read_le(&mut $reader)?;

                // Build the cases for all instructions.
                $(if Instruction::<N>::OPCODES[index as usize] == $variant::<N>::opcode() {
                    // Read the instruction.
                    let instruction = $variant::read_le(&mut $reader)?;
                    // Return the instruction.
                    return Ok(Self::$variant(instruction));
                })+
                // If the index is out of bounds, return an error.
                Err(error(format!("Failed to deserialize an instruction of opcode index '{index}'")))
            }};
        }
        // Execute the `from_bytes_le` method.
        crate::instruction!(instruction_from_bytes_le!(self, reader))
    }
}

impl<N: Network> ToBytes for Instruction<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        /// Creates a match statement that produces the `ToBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_to_bytes_le!(self, |writer| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_to_bytes_le {
            ($object:expr, |$writer:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // Build the match cases.
                match $object {
                    $(Self::$variant(instruction) => {
                        // Retrieve the opcode index.
                        // Note: This unwrap is guaranteed to succeed because the opcode variant is known to exist.
                        let index = Instruction::<N>::OPCODES.iter().position(|&opcode| $variant::<N>::opcode() == opcode).unwrap();

                        // Serialize the instruction.
                        u16::write_le(&(index as u16),&mut $writer)?;
                        instruction.write_le(&mut $writer)?;
                    }),+
                }
                Ok(())
            }};
        }
        // Execute the `to_bytes_le` method.
        crate::instruction!(instruction_to_bytes_le!(self, writer))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_bytes() -> Result<()> {
        let instruction = "add r0 r1 into r2;";
        let expected = Instruction::<CurrentNetwork>::from_str(instruction)?;
        let expected_bytes = expected.to_bytes_le()?;

        let candidate = Instruction::<CurrentNetwork>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
