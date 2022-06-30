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

impl<N: Network, A: circuit::Aleo<Network = N>> FromBytes for Instruction<N, A> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        /// Creates a match statement that produces the `FromBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_from_bytes_le!(self, |reader| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_from_bytes_le {
            ($object:expr, |$reader:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // A list of instruction enum variants.
                const INSTRUCTION_ENUMS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_ENUMS.len() <= u16::MAX as usize);

                // Read the enum variant index.
                let variant = u16::read_le(&mut $reader)?;

                // Build the cases for all instructions.
                $(if INSTRUCTION_ENUMS[variant as usize] == stringify!($variant) {
                    // Read the instruction.
                    let instruction = $variant::read_le(&mut $reader)?;
                    // Return the instruction.
                    return Ok(Self::$variant(instruction));
                })+
                // If the index is out of bounds, return an error.
                Err(error(format!("Failed to deserialize an instruction of variant {variant}")))
            }};
        }
        // Execute the `from_bytes_le` method.
        crate::instruction!(instruction_from_bytes_le!(self, reader))
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> ToBytes for Instruction<N, A> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        /// Creates a match statement that produces the `ToBytes` implementation for the given instruction.
        ///
        /// ## Example
        /// ```ignore
        /// instruction_to_bytes_le!(self, |writer| {}, { Add, Sub, Mul, Div })
        /// ```
        macro_rules! instruction_to_bytes_le {
            ($object:expr, |$writer:ident| $_operation:block, { $( $variant:ident, )+ }) => {{
                // A list of instruction enum variants.
                const INSTRUCTION_ENUMS: &[&'static str] = &[ $( stringify!($variant), )+];
                // Ensure the size is sufficiently large.
                assert!(INSTRUCTION_ENUMS.len() <= u16::MAX as usize);

                // Build the match cases.
                match $object {
                    $(Self::$variant(instruction) => {
                        // Retrieve the enum variant index.
                        // Note: This unwrap is guaranteed to succeed because the enum variant is known to exist.
                        let variant = INSTRUCTION_ENUMS.iter().position(|&name| stringify!($variant) == name).unwrap();

                        // Serialize the instruction.
                        u16::write_le(&(variant as u16),&mut $writer)?;
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
    use circuit::network::AleoV0;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;
    type CurrentAleo = AleoV0;

    #[test]
    fn test_instruction_bytes() -> Result<()> {
        let instruction = "add r0 r1 into r2;";
        let expected = Instruction::<CurrentNetwork, CurrentAleo>::from_str(instruction)?;
        let expected_bytes = expected.to_bytes_le()?;

        let candidate = Instruction::<CurrentNetwork, CurrentAleo>::from_bytes_le(&expected_bytes)?;
        assert_eq!(expected_bytes, candidate.to_bytes_le()?);
        Ok(())
    }
}
