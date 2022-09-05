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

impl<N: Network> FromBytes for Literal<N> {
    /// Reads the literal from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let index = u16::read_le(&mut reader)?;
        let literal = match index {
            0 => Self::Address(Address::read_le(&mut reader)?),
            1 => Self::Boolean(Boolean::read_le(&mut reader)?),
            2 => Self::Field(Field::read_le(&mut reader)?),
            3 => Self::Group(Group::read_le(&mut reader)?),
            4 => Self::I8(I8::read_le(&mut reader)?),
            5 => Self::I16(I16::read_le(&mut reader)?),
            6 => Self::I32(I32::read_le(&mut reader)?),
            7 => Self::I64(I64::read_le(&mut reader)?),
            8 => Self::I128(I128::read_le(&mut reader)?),
            9 => Self::U8(U8::read_le(&mut reader)?),
            10 => Self::U16(U16::read_le(&mut reader)?),
            11 => Self::U32(U32::read_le(&mut reader)?),
            12 => Self::U64(U64::read_le(&mut reader)?),
            13 => Self::U128(U128::read_le(&mut reader)?),
            14 => Self::Scalar(Scalar::read_le(&mut reader)?),
            15 => Self::String(StringType::read_le(&mut reader)?),
            16.. => return Err(error(format!("Failed to decode literal variant {index}"))),
        };
        Ok(literal)
    }
}

impl<N: Network> ToBytes for Literal<N> {
    /// Writes the literal to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        type Size = u16;
        match self {
            Self::Address(primitive) => {
                (0 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::Boolean(primitive) => {
                (1 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::Field(primitive) => {
                (2 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::Group(primitive) => {
                (3 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::I8(primitive) => {
                (4 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::I16(primitive) => {
                (5 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::I32(primitive) => {
                (6 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::I64(primitive) => {
                (7 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::I128(primitive) => {
                (8 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::U8(primitive) => {
                (9 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::U16(primitive) => {
                (10 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::U32(primitive) => {
                (11 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::U64(primitive) => {
                (12 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::U128(primitive) => {
                (13 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::Scalar(primitive) => {
                (14 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
            Self::String(primitive) => {
                (15 as Size).write_le(&mut writer)?;
                primitive.write_le(&mut writer)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u32 = 1000;

    fn check_bytes(expected: Literal<CurrentNetwork>) -> Result<()> {
        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, Literal::read_le(&expected_bytes[..])?);
        assert!(Literal::<CurrentNetwork>::read_le(&expected_bytes[1..]).is_err());
        // assert!(Literal::<CurrentNetwork>::read_le(&expected_bytes[2..]).is_err());
        Ok(())
    }

    #[test]
    fn test_bytes() -> Result<()> {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let private_key = snarkvm_console_account::PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;

            // Address
            check_bytes(Literal::<CurrentNetwork>::Address(Address::try_from(private_key)?))?;
            // Boolean
            check_bytes(Literal::<CurrentNetwork>::Boolean(Boolean::new(Uniform::rand(rng))))?;
            // Field
            check_bytes(Literal::<CurrentNetwork>::Field(Uniform::rand(rng)))?;
            // Group
            check_bytes(Literal::<CurrentNetwork>::Group(Uniform::rand(rng)))?;
            // I8
            check_bytes(Literal::<CurrentNetwork>::I8(I8::new(Uniform::rand(rng))))?;
            // I16
            check_bytes(Literal::<CurrentNetwork>::I16(I16::new(Uniform::rand(rng))))?;
            // I32
            check_bytes(Literal::<CurrentNetwork>::I32(I32::new(Uniform::rand(rng))))?;
            // I64
            check_bytes(Literal::<CurrentNetwork>::I64(I64::new(Uniform::rand(rng))))?;
            // I128
            check_bytes(Literal::<CurrentNetwork>::I128(I128::new(Uniform::rand(rng))))?;
            // U8
            check_bytes(Literal::<CurrentNetwork>::U8(U8::new(Uniform::rand(rng))))?;
            // U16
            check_bytes(Literal::<CurrentNetwork>::U16(U16::new(Uniform::rand(rng))))?;
            // U32
            check_bytes(Literal::<CurrentNetwork>::U32(U32::new(Uniform::rand(rng))))?;
            // U64
            check_bytes(Literal::<CurrentNetwork>::U64(U64::new(Uniform::rand(rng))))?;
            // U128
            check_bytes(Literal::<CurrentNetwork>::U128(U128::new(Uniform::rand(rng))))?;
            // Scalar
            check_bytes(Literal::<CurrentNetwork>::Scalar(Uniform::rand(rng)))?;
            // String
            check_bytes(Literal::<CurrentNetwork>::String(StringType::rand(rng)))?;
        }
        Ok(())
    }
}
